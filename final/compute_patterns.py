#!/usr/bin/python
"""
	(c) 2023 by Manfred Scheucher and Helena Bergold
"""

from itertools import *
from sys import argv

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("rank",type=int,help="rank")
args = parser.parse_args()

print("args",args)

rank = args.rank
n = 2*rank
N = list(range(n))


def lexmax_cyclic4(p):
	for i in range(len(p),4):
		p_rot = p[i:]+p[:i]
		if p < p_rot: return False
	return True

def pattern_extensions(p):
	for i in range(len(p)):
		if p[i-4:i] == '||xx':
			assert(i >= 4) # will not happend
			yield p[:i-4]+'||||xxxx'+p[i:]
		if p[i-4:i] == 'x||x':
			assert(i >= 4) # will not happend
			yield p[:i-4]+'x|||xx|x'+p[i:]

def compute_patterns(r):
	assert(r%2 == 0 and r >= 4)
	if r == 4: 
		return {'|||xx|xx','||xx|xx|','xx|x||x|'}
	if r >= 6: 
		patterns = {'||xxxx|x||x|'} if r == 6 else set()
		for p in compute_patterns(r-2):
			patterns |= set(pattern_extensions(p))
		for p in patterns: 
			assert(lexmax_cyclic4(p)) # test that there are no cyclic copies, just to be sure
		return patterns


ct = 0
for p in sorted(compute_patterns(rank)):
	ct+=1
	q = [x+1 for x in N if p[x]=='x']
	print(ct,"->",p,q)
