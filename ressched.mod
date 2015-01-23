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
    # {1.. numOffsites}, {numOffsites + 1.. numSph}, {numOffsites + numSph + 1.. numOffsites + numSph + numVgh}
    # in other words, first comes the offsite set (containing its juniors), then the vghOnSiteSet (containing its
    # juniors), and then sphOnSiteSet (containing its juniors)

    set vghOnSiteSet within vghSet :=  {numOffsites + 1 .. numOffsites + numVgh};
    set sphOnSiteSet within sphSet := {numOffsites + numVgh + 1 .. numOffsites + numSph + numVgh};
    
    set vghOnSiteJrSet within vghSet := {numOffsites + 1 .. numOffsites + numVghJr};
    set sphOnSiteJrSet within sphSet := {numOffsites + numVgh + 1 .. numOffsites + numVgh + numSphJr};

    set sphJrSet within sphSet := offsiteJrSet union sphOnSiteJrSet;
    set vghJrSet within vghSet := offsiteJrSet union vghOnSiteJrSet;


    var sph{d in daySet, r in sphSet} binary;    
    var vgh{d in daySet, r in vghSet} binary;
    minimize onCallShifts: sum{d in daySet, r in sphSet}sph[d,r] + sum{d in daySet, r in vghSet}vgh[d,r];
     

/* 
		constraints 
        type 0: vgh cannot work at sph and vice-versa
		type 1: offsites can only be in one place at a time
		type 2: all residents need at least two days off between shifts 
		type 3: weekends require 2 people, weekdays 3, for both locations 
		type 4: max one junior per site per shift 
		type 5: offsites can only work one day a month and it has to be a weekend day 
        type 6: on-sites work max two weekend days and a max number of shifts per month
		type 7: holiday requests, etc. 
*/

    subject to constraint0a: sum{d in daySet, r in sphOnSiteSet} vgh[d,r] = 0;
    subject to constraint0b: sum{d in daySet, r in vghOnSiteSet} sph[d,r] = 0;

    subject to constraint1a {d in daySet, r in offsiteSet}: sph[d,r] + vgh[d,r] <= 1;

    subject to constraint2a {d in daySet, r in sphSet: d+2 <= studyLength}: sph[d,r] + sph[d+1,r] + sph[d+2,r] <= 1;
    subject to constraint2b {d in daySet, r in vghSet: d+2 <= studyLength}: vgh[d,r] + vgh[d+1,r] + vgh[d+2,r] <= 1;

    subject to constraint3a {d in weekendSet}: sum{r in sphSet}sph[d,r] = 2;
    subject to constraint3b {d in weekendSet}: sum{r in vghSet}vgh[d,r] = 2;
    subject to constraint3c {d in weekdaySet}: sum{r in vghSet}vgh[d,r] = 3;
    subject to constraint3d {d in weekdaySet}: sum{r in sphSet}sph[d,r] = 3;

    subject to constraint4a {d in daySet}: sum{r in sphJrSet} sph[d,r] <= 1;
    subject to constraint4b {d in daySet}: sum{r in vghJrSet} vgh[d,r] <= 1;

    subject to constraint5a {r in offsiteSet}: sum{d in weekendSet}(sph[d,r] + vgh[d,r]) <= 1;    
    subject to constraint5b {r in offsiteSet}: sum{d in weekdaySet}(sph[d,r] + vgh[d,r]) = 0;

    subject to constraint6a{r in vghSet}:sum{d in weekendSet}vgh[d,r] <= maxWeekendShifts;
    subject to constraint6b{r in sphSet}:sum{d in weekendSet}sph[d,r] <= maxWeekendShifts;
    
    subject to constraint6c{r in vghSet}:sum{d in daySet}vgh[d,r] <= maxMonthlyShifts;
    subject to constraint6d{r in sphSet}:sum{d in weekendSet}sph[d,r] <= maxMonthlyShifts;
    
    subject to constraint6e{r in sphOnSiteSet}:sum{d in daySet}sph[d,r] <= maxMonthlyShifts;
    subject to constraint6f{r in sphOnSiteSet}:sum{d in daySet}sph[d,r] >= minMonthlyShifts;
    
    subject to constraint6g{r in vghOnSiteSet}:sum{d in daySet}vgh[d,r] <= maxMonthlyShifts;
    subject to constraint6h{r in vghOnSiteSet}:sum{d in daySet}vgh[d,r] >= minMonthlyShifts;

# person-specific constraints 
# this is the bulk holiday schedule that is pasted below

    subject to constraint7a{d in daySet, r in vghSet}: vgh[d,r] <= vacay_restrictions[d,r];
    subject to constraint7b{d in daySet, r in sphSet}: sph[d,r] <= vacay_restrictions[d,r];

    

 solve;

# a table statement that allows a different way of outputting the data, currently commented out 
#  table tout{d in daySet, r in vghSet} OUT "CSV" "output.csv" : d, r, vgh[d,r];
 end;
