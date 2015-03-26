/* 
    A scheduling problem. 

    We want to schedule medical residents to achieve a feasible shift schedule. 

    There are two types of resident: {senior, junior}
    There are three pools to pull from {sph, vgh, offsite}
    There are two schedules to fill: {sph, vgh}
    
  */
 
    param minMonthlyShifts;
    param maxMonthlyShifts;
    param maxWeekendShifts;
    param studyLength;     
    param numOffsites;      
    param numVgh;    	   
    param numSph; 
    param numSphJr;
    param numVghJr;
    param numOffsiteJr;

    set daySet := {1..studyLength}; 
    set weekendSet; # Fridays, Saturdays, Sundays, holidays are weekends, to be specified in data block
    set weekdaySet := daySet diff weekendSet; 

    # for overall sph and vgh we have a vector of all eligible residents for both sites
    # we will later restrict so that e.g. vgh residents cannot work at sph and vice-versa 
    set sphSet := {1..(numOffsites + numSph + numVgh)};
    set vghSet := {1..(numOffsites + numSph + numVgh)};

    set offsiteSet := {1..numOffsites};    
    # we will assume that offsites form the first n entries 
    set offsiteJrSet within offsiteSet := {1..numOffsiteJr};

    # holiday restrictions that are set in a tabular format; both vghSet and sphSet 
    # are indexed the same so we can just index by sphSet
    param vacay_restrictions{d in daySet, r in sphSet};    

    # sphSet and vghSet are each assumed to be indexed as follows:
    # {1.. numOffsites}, {numOffsites + 1.. numVgh}, {numOffsites + numVgh + 1.. numOffsites + numSph + numVgh}
    # in other words, first comes the offsite set (containing its juniors), then the vghOnSiteSet (containing its
    # juniors), and then sphOnSiteSet (containing its juniors)

    set vghOnSiteSet within vghSet :=  {numOffsites + 1 .. numOffsites + numVgh};
    set sphOnSiteSet within sphSet := {numOffsites + numVgh + 1 .. numOffsites + numSph + numVgh};
    
    set vghOnSiteJrSet within vghSet := {numOffsites + 1 .. numOffsites + numVghJr};
    set sphOnSiteJrSet within sphSet := {numOffsites + numVgh + 1 .. numOffsites + numVgh + numSphJr};

    set sphJrSet within sphSet := offsiteJrSet union sphOnSiteJrSet;
    set vghJrSet within vghSet := offsiteJrSet union vghOnSiteJrSet;

    set vghOnSiteSrSet within vghSet := vghOnSiteSet diff vghOnSiteJrSet;
    set sphOnSiteSrSet within sphSet := sphOnSiteSet diff sphOnSiteJrSet;


    var sph{d in daySet, r in sphSet} binary;    
    var vgh{d in daySet, r in vghSet} binary;
    # minimize onCallShifts: sum{d in daySet, r in sphSet}sph[d,r] + sum{d in daySet, r in vghSet}vgh[d,r];
    # KLG changed on 24 Mar 2015 to place highest priority on Offsites, then Jrs relative to Srs
    minimize onCallShifts: sum{d in daySet, r in offsiteSet}(sph[d,r] + vgh[d,r]) 
                        + 10*(sum{d in daySet, r in vghOnSiteJrSet}vgh[d,r] + sum{d in daySet, r in sphOnSiteJrSet}sph[d,r]) + 100*(sum{d in daySet, r in vghOnSiteSrSet}vgh[d,r] + sum{d in daySet, r in sphOnSiteSrSet}sph[d,r]);
   

/* 
		constraints 
        - vgh cannot work at sph and vice-versa
		- offsites can only be in one place at a time (sph or vgh but not both)
		- all residents need at least two days off between shifts 
		- weekends require 2 people, weekdays 3, for both locations 
		- max one junior per site per shift 
		- offsites can only work one day a month and it has to be a weekend day 
        - on-sites work a configurable max weekend days and a max number of shifts per month
		- call requests
*/
    subject to 
    noSphAtVgh: sum{d in daySet, r in sphOnSiteSet} vgh[d,r] = 0;
    noVghAtSph: sum{d in daySet, r in vghOnSiteSet} sph[d,r] = 0;

    onePlaceAtATime {d in daySet, r in offsiteSet}: sph[d,r] + vgh[d,r] <= 1;

    RestPeriodSph {d in 1.. studyLength - 2, r in sphSet}:sum{i in d..d+2} sph[i,r] <= 1;
    RestPeriodVgh {d in daySet, r in vghSet: d+2 <= studyLength}: vgh[d,r] + vgh[d+1,r] + vgh[d+2,r] <= 1;
    
    # the amount of people on per shift. 2 on weekends, 3 on weekdays 
    WeekendShiftsSph {d in weekendSet}: sum{r in sphSet}sph[d,r] = 2;
    WeekendShiftsVgh {d in weekendSet}: sum{r in vghSet}vgh[d,r] = 2;
    WeekdayShiftsVgh {d in weekdaySet}: sum{r in vghSet}vgh[d,r] = 3;
    WeekdayShiftsSph {d in weekdaySet}: sum{r in sphSet}sph[d,r] = 3;

    
    # we will allow Seniors to cover Junior shifts, but the objective function will penalize it
    JrShiftsSph {d in daySet}: sum{r in sphJrSet} sph[d,r] <= 1;
    JrShiftsVgh {d in daySet}: sum{r in vghJrSet} vgh[d,r] <= 1;
    
    offSiteWeekendShifts {r in offsiteSet}: sum{d in weekendSet}(sph[d,r] + vgh[d,r]) <= 1;    
    offSiteWeekdayShifts {r in offsiteSet}: sum{d in weekdaySet}(sph[d,r] + vgh[d,r]) = 0;

    MaxWeekendShiftsVgh {r in vghSet}:sum{d in weekendSet} vgh[d,r] <= maxWeekendShifts;
    MaxWeekendShiftsSph {r in sphSet}:sum{d in weekendSet} sph[d,r] <= maxWeekendShifts;
      
    MaxMonthlyShiftsSph {r in sphOnSiteSet}:sum{d in daySet}sph[d,r] <= maxMonthlyShifts;
    MaxMonthlyShiftsVgh {r in vghOnSiteSet}:sum{d in daySet}vgh[d,r] <= maxMonthlyShifts;


    MinMonthlyShiftsVgh {r in vghOnSiteSet}:sum{d in daySet}vgh[d,r] >= minMonthlyShifts;
    MinMonthlyShiftsSph {r in sphOnSiteSet}:sum{d in daySet}sph[d,r] >= minMonthlyShifts;

# person-specific constraints 
# this is the bulk holiday schedule that is pasted below

    CallRequestsVgh {d in daySet, r in vghSet}: vgh[d,r] <= vacay_restrictions[d,r];
    CallRequestsSph {d in daySet, r in sphSet}: sph[d,r] <= vacay_restrictions[d,r];

   # they are on at vgh so should already be zeroed in sph schedule 
   aiza: sph[18,35] = 1;



 solve;
display onCallShifts;

/*
   display offsiteSet;
   display vghOnSiteSet;
   display vghOnSiteSrSet;
   display  sphOnSiteSet;
   display sphOnSiteSrSet;
*/



 end;
