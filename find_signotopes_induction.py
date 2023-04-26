#!/usr/bin/python
"""
	(c) 2022 by Manfred Scheucher and Helena Bergold
"""

from itertools import *
from sys import argv


from basics import *
import datetime


time_start = datetime.datetime.now()


import argparse
parser = argparse.ArgumentParser()
parser.add_argument("rank",type=int,help="rank")

parser.add_argument("-fp","--filepath",type=str,help="file to load signotope on rank r-2")
parser.add_argument("-fl","--filelinenumber",type=int,default=0,help="line in file to load signotope on rank r-2")


parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")


parser.add_argument("--instance2file","-i2f",type=str,help="write instance to file")
parser.add_argument("--solutions2file","-s2f",type=str,help="write solutions to file")
parser.add_argument("--dontsolve",action='store_true',help="do not solve instance")

parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")
args = parser.parse_args()

print("args",args)


rank = args.rank
n = 2*rank
N = list(range(n))

even = list(range(0,n,2))
odd  = list(range(1,n,2))


args.filepath = "examples/x"+str(rank-2)



rank_plus_one_types_all = [s for s in ["".join(s) for s in product('+-',repeat=rank+1)] if s.count('+-')+s.count('-+') <= 1]

print ("number of rank_plus_one_types_all:",len(set(rank_plus_one_types_all)))

def string_flip(t,i): return t[:i]+('+' if t[i] == '-' else '-')+t[i+1:]

# in the following types, index j is flipable
rank_plus_one_types_with_flipable_j = {j:[t for t in rank_plus_one_types_all if string_flip(t,j) in rank_plus_one_types_all] for j in range(rank+1)}

def type_to_vector(t): return [(+1 if x == '+' else -1) for x in t]

_minrot = dict()
def minrot(I,signed=False):
	if I not in _minrot:
		assert(len(I) == rank)
		_minrot[I] = min((tuple(sorted([(x+k)%n for x in I])),(-1)**len([x for x in I if x+k >= n])) for k in range(0,n,4))
	return _minrot[I] if signed else _minrot[I][0]


_I_extension_at_j = dict()
_J_relevant = set()
for I in combinations(N,rank):
	if I == minrot(I):		
		I_plus = (-1,)+I+(n,)
		_I_extension_at_j[I] = {j:[I[:j]+(x,)+I[j:] for x in range(I_plus[j]+1,I_plus[j+1])] for j in range(rank+1)}
		for j in range(rank+1):
			_J_relevant |= set(_I_extension_at_j[I][j])


all_variables = []
if 1:
	all_variables += [('sign',I) for I in combinations(N,rank) if I == minrot(I)]
	all_variables += [('flip',I)  for I in combinations(N,rank) if I == minrot(I)] # indicates whether (rank)-tuple is flipable
	
	all_variables += [('type',(J,t)) for J in _J_relevant for t in rank_plus_one_types_all] # indicates whether (rank+1)-tuple is of type t
	all_variables += [('flipj',(J,j)) for J in _J_relevant for j in range(rank+1)] # indicates whether, in (rank+1)-tuple, index j is flipable


print ("total number of variables:",len(all_variables))

all_variables_index = {}

_num_vars = 0
for v in all_variables:
	all_variables_index[v] = _num_vars
	_num_vars += 1

def var(L):	return 1+all_variables_index[L]

#def var_sign(*L): return var(('sign',L))


def var_sign(*I): 
	J,s = minrot(I,signed=True)
	return s*var(('sign',J))

def var_flipable(*I): 
	return var(('flip',minrot(I)))

def var_rank_plus_one_type(J,j): return var(('type',((J),j)))
def var_flipable_j(J,j): return var(('flipj',((J),j)))


constraints = []


if 1:
	prescribed_fliples = set()
	prescribed_fliples.add(tuple(even))
	prescribed_fliples.add(tuple(odd))

	if rank % 4 == 0:
		I = list(range(2,rank+3)) # ||xx...xx|x| ||||
		del I[-3]
		print("fix fliple",I)
		prescribed_fliples.add(tuple(I))

		I = list(range(3,rank+4)) # |||xx...xx|x ...
		del I[-3]
		print("fix fliple",I)
		prescribed_fliples.add(tuple(I))

		if rank >= 8:
			I = list(range(0,rank+3))
			del I[-2]
			del I[-2]
			del I[-3]
			print("fix fliple",I)
			prescribed_fliples.add(tuple(I))

			# the following is a restriction!
			I = list(range(1,rank+4))
			del I[-2]
			del I[-4]
			del I[-5]
			print("fix fliple",I)
			prescribed_fliples.add(tuple(I))

		if rank == 8:
			I = (0,1,3,7,8,10,14,15)
			print("fix fliple",I)
			prescribed_fliples.add(I)

		if rank == 12:
			I = (8,9,10,11,12,13,14,15,16,17,19,22) # eins von den oberen?
			print("fix fliple",I)
			prescribed_fliples.add(I)

			I = (6,7,8,9,10,11,12,13,15,19,20,22) 
			print("fix fliple",I)
			prescribed_fliples.add(I)

			I = (5,6,7,8,9,10,11,12,14,16,17,19)
			print("fix fliple",I)
			prescribed_fliples.add(I)

			I = (4,5,6,7,8,9,11,17,18,19,20,22)
			print("fix fliple",I)
			prescribed_fliples.add(I)

			I = (2,3,4,5,7,15,16,17,18,19,20,22)
			print("fix fliple",I)
			prescribed_fliples.add(I)

		if rank >= 16:
			exit("TODO")


	if rank % 4 == 2:
		I = list(range(0,rank+1))
		del I[-3]
		print("fix fliple",I)
		prescribed_fliples.add(tuple(I))

		I = list(range(1,rank+2))
		del I[-3]
		print("fix fliple",I)
		prescribed_fliples.add(tuple(I))

		assert(rank >= 6)
		I = list(range(2,rank+5))
		del I[-2]
		del I[-2]
		del I[-3]
		print("fix fliple",I)
		prescribed_fliples.add(tuple(I))

		# the following is a restriction!
		I = list(range(3,rank+6))
		del I[-2]
		del I[-4]
		del I[-5]
		print("fix fliple",I)
		prescribed_fliples.add(tuple(I))

		if rank == 10:
			I = (0,1,2,3,4,5,7,11,12,14)
			print("fix fliple",I)
			prescribed_fliples.add(I)

			I = (0,1,3,9,10,11,12,14,18,19)
			print("fix fliple",I)
			prescribed_fliples.add(I)

		if rank >= 14:
			exit("TODO")


	assert(rank >= 6)

	# compute closure under 4-fold rotationsmaxnumfliples
	prescribed_fliples = {tuple(sorted([(x+k)%n for x in I])) for I in prescribed_fliples for k in range(0,n,4)}
	wanted_number_of_fliples = (rank//2)**2+(rank//2)+2
	#print("prescribed_fliples",prescribed_fliples,"of",wanted_number_of_fliples)
	assert(len(prescribed_fliples) == wanted_number_of_fliples)


	for I in combinations(N,rank):
		if I in prescribed_fliples: 
			constraints.append([+var_flipable(*I)])
		else:
			constraints.append([-var_flipable(*I)])




assert(args.filepath)
if args.filepath:
	print("* LOAD r-2 signotope from file:",args.filepath)
	print("* line:",args.filelinenumber)

	Xstr = open(args.filepath).readlines()[args.filelinenumber]
	if Xstr[-1] == '\n': Xstr = Xstr[:-1]
	assert(len(Xstr) == len(list(combinations(range(n-4),rank-2))))

	for x in range(0,n,4):
		Ndeleted = [x,x+2]
		Ncontracted = [x+1,x+3]

		Nremaining = list(sorted(set(N)-set(Ndeleted)-set(Ncontracted)))
		X = string_to_signotope(Xstr,elements=Nremaining,rank=rank-2)

		for I in X:
			I_ext = tuple(sorted(list(I)+Ncontracted))
			constraints.append([+var_sign(*I_ext)*X[I]])



print ("(*) each (rank+1)-tuple has one type")
for J in _J_relevant:
	constraints.append([+var_rank_plus_one_type(J,t) for t in rank_plus_one_types_all])

def remove_jth(I,j): return I[:j]+I[j+1:]


print ("(*) assign rank_plus_one_type variables")
for J in _J_relevant:
	for t in rank_plus_one_types_all:
		tv = type_to_vector(t)
		for j in range(rank+1):
			constraints.append([-var_rank_plus_one_type(J,t),+tv[j]*var_sign(*remove_jth(J,rank-j))])
		constraints.append([+var_rank_plus_one_type(J,t)]+[-tv[j]*var_sign(*remove_jth(J,rank-j)) for j in range(rank+1)])



print ("(*) assign flipable variables")
for I in combinations(N,rank):
	if I == minrot(I):		
		I_plus = (-1,)+I+(n,)
		I_extension_at_j = _I_extension_at_j[I]

		for j in range(rank+1):
			for J in I_extension_at_j[rank-j]: 
				constraints.append([-var_flipable(*I),+var_flipable_j(J,j)])

		constraints.append([+var_flipable(*I)]+[-var_flipable_j(J,j) for j in range(rank+1) for J in I_extension_at_j[rank-j]])


print ("(*) assign flipable_j variables")
for J in _J_relevant:
	for j in range(rank+1):
		constraints.append([-var_flipable_j(J,j)]+[+var_rank_plus_one_type(J,t) for t in rank_plus_one_types_with_flipable_j[j]])

		for t in rank_plus_one_types_with_flipable_j[j]: 
			constraints.append([+var_flipable_j(J,j),-var_rank_plus_one_type(J,t)])
	



if 1:
	print ("(*) Levi: 1 -- (rank-1) assignments")
	for A in combinations(even,1):
		for B in combinations(odd,rank-1):
			I = tuple(sorted(A+B))
			iA0 = I.index(A[0])
			sign = +(-1)**iA0
			constraints.append([+var_sign(*I)*sign])

	for A in combinations(even,rank-1):
		for B in combinations(odd,1):
			I = tuple(sorted(A+B))
			iB0 = I.index(B[0])
			sign = -(-1)**iB0
			constraints.append([+var_sign(*I)*sign])


if 0:
	# this is implied by the other conditions above
	print ("(*) Levi: 2 -- (rank-2) assignments")
	for A in combinations(even,2):
		for B in combinations(odd,rank-2):
			I = tuple(sorted(A+B))
			iA0 = I.index(A[0])
			iA1 = I.index(A[1])
			if (iA0 + iA1)%2 == 0: 
				sign = +(-1)**iA0
				constraints.append([+var_sign(*I)*sign])

	for A in combinations(even,rank-2):
		for B in combinations(odd,2):
			I = tuple(sorted(A+B))
			iB0 = I.index(B[0])
			iB1 = I.index(B[1])
			if (iB0 + iB1)%2 == 0: 
				sign = -(-1)**iB0
				constraints.append([+var_sign(*I)*sign])


if 1: # condition is fulfilled anyhow
	print ("(*) assumption: fliples are either all odd, all even, or half-half")
	for I in combinations(N,rank):
		if len(set(I) & set(even)) not in {0,rank//2,rank}:
			constraints.append([-var_flipable(*I)])



print ("total number of constraints:",len(constraints))
time_before_solving = datetime.datetime.now()
print("creating time:",time_before_solving-time_start)
print ()


if args.instance2file:
	fp = args.instance2file #"_instance_rank"+str(rank)+"_n"+str(n)+"_m"+str(m)+".cnf"
	print ("write instance to file",fp)
	
	f = open(fp,"w")
	f.write("p cnf "+str(_num_vars)+" "+str(len(constraints))+"\n")
	for c in constraints:
		f.write(" ".join(str(v) for v in c)+" 0\n")
	f.close()

	print ("Created CNF-file:",fp)
	


if not args.dontsolve:
	print ("start solving")
	ct = 0

	if args.solutions2file:
		print ("write solutions to file",args.solutions2file)
		outfile = open(args.solutions2file,"w")
	else:
		outfile = None

	if args.solver == "cadical":
		print ("use pysat/Cadical")
		from pysat.solvers import Cadical	
		solver = Cadical()
		for c in constraints: solver.add_clause(c)
		solution_iterator = solver.enum_models()
	else:
		print ("use pycosat")
		import pycosat
		solution_iterator = pycosat.itersolve(constraints)

	print (datetime.datetime.now(),"start solving")
	for sol in solution_iterator: 
		ct += 1
		s = "".join("+" if var_sign(*I) in sol else "-" for	I in combinations(N,rank))

		print (datetime.datetime.now(),"solution #",ct,"found")#,"\t",s)
		if outfile: 
			outfile.write(s+"\n")
			outfile.flush()

		X = string_to_signotope(s,N,rank)
		if not args.all: break


	time_end = datetime.datetime.now()

	if ct == 0:
		print (time_end,"no solution!?")
	else:
		if args.all:
			print (time_end,"total count:",ct)
		else:
			print("use parameter -a/--all to enumerate all solutions")

	if outfile: print ("wrote solutions to file:",args.solutions2file)
	
