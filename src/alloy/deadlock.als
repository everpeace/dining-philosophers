module deadlock

open problem_setting as env
open util/ordering[State]

-- Naive algorithm with deadlocks:
-- philosophers are very eagerly.
-- every philosopher releases forks only when eating.
-- only one philosoper moves in one step. (C-Daemon)
pred CanTakeLeft(s: State, p: Philosopher){
	free[s,p.leftFork]
}
pred TakeLeft ( s: State, s': State, p: Philosopher ) {
	CanTakeLeft[s,p] and s'.owned[p.leftFork] = p
	and (all f: (Fork - p.leftFork) | s.owned[f] = s'.owned[f])
}
pred CanTakeRight(s:State, p:Philosopher){
	free[s,p.rightFork]
}
pred TakeRight ( s: State, s': State, p: Philosopher ) {
	CanTakeRight[s,p] and s'.owned[p.rightFork] = p
	and (all f: (Fork - p.rightFork) | s.owned[f] = s'.owned[f])
}
pred CanRelease(s:State, p:Philosopher){
	eating[s,p]
}
pred Release(s:State, s':State, p:Philosopher){
	CanRelease[s,p] and (free[s',p.rightFork] and free[s',p.leftFork])	
	and (all f: (Fork - (p.leftFork + p.rightFork)) | s.owned[f] = s'.owned[f])
}

-- definition for order of states
pred init ( s: State ) {
	all f: Fork | free [ s, f ]
}
pred NextState ( s: State, s': State ) {
	some p: Philosopher | TakeLeft [ s, s', p ] or TakeRight [ s, s', p ] or Release[s,s',p] 
}
pred CanMove(s:State){
	some p: Philosopher | 
		CanTakeLeft[s,p] or CanTakeRight[s,p] or CanRelease[s,p]
}
fact Traces {
	init [ first ] 
	all s: State - last
		| CanMove[s] => NextState[s,next[s]] else s.owned = next[s].owned
} 

-- considering only fair execution
-- i.e. the number of moves of every philosopher is the same with others.
fun PhilosopherMovesAt(s:State): lone Philosopher{
	(s = last or not CanMove[s]) => none
	else s.owned in next[s].owned => (next[s].owned-s.owned)[Fork]
    		else (s.owned - next[s].owned)[Fork] 
}
fun NumberOfMoves(p:Philosopher):Int{
	sum s:State | #(p&PhilosopherMovesAt[s])
}
fact FairExecution{
	all disj p,q:Philosopher | NumberOfMoves[p] = NumberOfMoves[q]
}

-- The number of State must be an kN+1,
-- where N is the number of forks and k is a natural number.
assert noDeadLock{
	all s:State | CanMove[s]
}
check noDeadLock for exactly 5 Fork, 5 Philosopher,  6 State
