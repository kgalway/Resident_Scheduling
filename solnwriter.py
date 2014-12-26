"""

solution parser for resident scheduling problem 


"""
from collections import defaultdict
import sys

def parse_soln_file():

    infile = 'solnfile.dat'
    with open(infile,'r') as f:
        soln = f.readlines()
    f.close()
    sph = defaultdict(list)
    vgh = defaultdict(list)

    soln = [x for x in soln if 'sph' in x or 'vgh' in x]
    soln = [x.split() for x in soln]
    for x in soln:
        if int(x[3]) == 1:
            y = x[1]
            z = y.split('[')
            z = z[1].split(',')
            day = z[0]
            z = z[1].split(']')
            person = z[0]
       
            if x[1][0]=='s':            
                sph[day].append(person)
            else:            
                vgh[day].append(person) 
    return (sph,vgh)	

def write_schedule_with_index(inp):
    (sph,vgh) = inp
    outfile  = 'schedule.csv'
    with open(outfile,'w') as f:
        f.write('SPH Schedule Follows\nDay,Resident1,Resident2,Resident3\n')
        for key in sph:
            f.write(str(key))
            for val in sph[key]:
                f.write(','+str(val))
            f.write('\n')
        f.write('VGH schedule follows\n')
        f.write('Day, Resident1, Resident2, Resident3\n')
        for key in vgh:
            f.write(str(key))
            for val in vgh[key]:
                f.write(',' + str(val))
            f.write('\n')
    f.close()
    return None

def read_map():

    sph_key = {}
    vgh_key = {}
    with open('block_key.csv','r') as f:
	    for line in f:
		    row = line.split(',')
		    sph_key[row[0]] = row[1]
    f.close()

    for key in sph:
        vgh[key] = sph[key]
    sph_key = {key:value.strip() for key,value in sph_key.items()}
    vgh_key = {key:value.strip() for key,value in vgh_key.items()}
    return (sph_key, vgh_key)

def write_schedule_with_names(inp1, inp2):
    sph_key, vgh_key = inp1
    sph, vgh = inp2


    with open('sph.csv','r') as f:
	    sph = f.readlines()
    f.close()
    sph = sph[1:]
    with open('vgh.csv','r') as f:
	    vgh = f.readlines()
    f.close()
    vgh = vgh[1:]

    sph = [x.strip().split(',') for x in sph]
    vgh = [x.strip().split(',') for x in vgh]

    new_sph = []
    for item in sph:
        day = item[0]
        if len(item) == 4:
    	    new_sph.append([item[0], sph_key[item[1]], sph_key[item[2]], sph_key[item[3]]])
        else:
    	   new_sph.append([item[0], sph_key[item[1]], sph_key[item[2]]])

    new_vgh = []
    for item in vgh:
        day = item[0]
        if len(item) == 4:
    	    new_vgh.append([item[0], vgh_key[item[1]], vgh_key[item[2]], vgh_key[item[3]]])
        else:
    	    new_vgh.append([item[0], vgh_key[item[1]], vgh_key[item[2]]])

    new_sph = {int(x[0]):x[1:] for x in new_sph}
    new_vgh = {int(x[0]):x[1:] for x in new_vgh}
    
    days = new_sph.keys()
    days.sort()

    with open('sph.csv','w') as f:
	    f.write('SPH Schedule\n')
	    f.write('day, resident, resident, resident\n')
	    for day in days:
	        row = str(day)
	        for item in new_sph[day]:
	        	row += ',' + item
	        f.write(row + '\n')		    		    
    f.close()

    days = new_vgh.keys()
    days.sort()

    with open('vgh.csv','w') as f:
	    f.write('VGH Schedule\n')
	    f.write('day, resident, resident, resident\n')
	    for day in days:
	        row = str(day)
	        for item in new_vgh[day]:
	        	row += ',' + item	        
	        f.write(row + '\n')		 		    
    f.close()

def write_call_counts(inp1,inp2):
	sph, vgh = inp1
	sph = sph.values()
	vgh = vgh.values()
	
	sph_key, vgh_key = inp2 

	sphCounts = defaultdict(int)
	vghCounts = defaultdict(int)

	for line in sph:
		for item in line:
			sphCounts[item]+=1

	for line in vgh:
		for item in line:
			vghCounts[item]+=1
	sphkeys = sphCounts.keys()	
	sphkeys.sort()

	vghkeys = vghCounts.keys()
	vghkeys.sort()

	with open('sph_counts.csv','w') as f:
		for key in sphkeys:
			row = sph_key[key] + ',' + str(sphCounts[key])
			f.write(row + '\n')
	f.close()

	with open('vgh_counts.csv','w') as f:
		for key in vghkeys:
			row = vgh_key[key] + ',' + str(vghCounts[key])
			f.write(row + '\n')
	f.close()



if __name__ == '__main__':

	(sph,vgh) = parse_soln_file()
	write_schedule_with_index((sph, vgh))
#	(sph_key, vgh_key) = read_map()
#	write_schedule_with_names((sph_key, vgh_key),(sph,vgh))
#	write_call_counts((sph,vgh),(sph_key,vgh_key))
	sys.exit()
