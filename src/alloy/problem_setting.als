module dining_philosophers/problem_setting

sig Philosopher { 
	disj leftFork, rightFork: one Fork,
	disj left, right: one Philosopher
}

sig Fork { 
	disj left, right: one Philosopher
}

fact ProblemSetting {
	#Philosopher > 2 
	#Fork > 2
	#Philosopher = #Fork
	--fork and philosophers are set properly
	(all p: Philosopher | p.leftFork = p.left.rightFork and p.rightFork = p.right.leftFork )
	(all f: Fork | f = f.left.rightFork and f = f.right.leftFork)
	-- one table
	(all p: Philosopher | Philosopher in p.^right and Philosopher in p.^left)
	(all f: Fork | Fork in f.^( left.leftFork ) and Fork in f.^( right.rightFork ))
}

-- Global State
sig State { 
	owned: Fork -> lone Philosopher
}{
	-- each fork is owned by only their neighbors.
	all f:Fork | owned[f] in f.(left+right)
}
-- predicates for forks
pred free ( s: State, f: Fork ) {
	no s.owned [ f ]
}

-- predicate for philosophers
pred eating ( s: State, p: Philosopher ) {
	p  = s.owned[p.rightFork] and p =  s.owned[p.leftFork]
}
