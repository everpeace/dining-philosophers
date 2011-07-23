module deadlock

open problem_setting
open util/ordering[State]

-- definitions for philosopher's move
pred canTakeLeft(s: State, p: Philosopher){
	free[s,p.leftFork]
}
pred takeLeft ( s: State, s': State, p: Philosopher ) {
	canTakeLeft[s,p] and s'.owned[p.leftFork] = p
	and (all f: (Fork - p.leftFork) | s.owned[f] = s'.owned[f])
}
pred canTakeRight(s:State, p:Philosopher){
	free[s,p.rightFork]
}
pred takeRight ( s: State, s': State, p: Philosopher ) {
	canTakeRight[s,p] and s'.owned[p.rightFork] = p
	and (all f: (Fork - p.rightFork) | s.owned[f] = s'.owned[f])
}
pred canReleaseLeft(s:State, p:Philosopher){
	p= s.owned[p.leftFork] and not eating[s,p]
}
pred releaseLeft(s:State, s':State, p:Philosopher){
	canReleaseLeft[s,p] and free[s',p.leftFork]
	and (all f: (Fork - (p.leftFork)) | s.owned[f] = s'.owned[f])
}
pred canRelease(s:State, p:Philosopher){
	eating[s,p]
}
pred release(s:State, s':State, p:Philosopher){
	canRelease[s,p] and (free[s',p.rightFork] and free[s',p.leftFork])	
	and (all f: (Fork - (p.leftFork + p.rightFork)) | s.owned[f] = s'.owned[f])
}

-- definition for order of states and Time
pred init ( s: State ) {
	all f: Fork | free [ s, f ]
}
pred nextState ( s: State, s': State ) {
	some p: Philosopher | takeLeft [ s, s', p ] or takeRight [ s, s', p ] or release[s,s',p] 
}
fact traces {
 init [ first ] 
 all s: State - last
 | canMove[s] => nextState[s,next[s]]
    else s.owned = next[s].owned
} 

-- consraints for fair execution
pred canMove(s:State){
	some p: Philosopher | 
		canTakeLeft[s,p] or canTakeRight[s,p] or canRelease[s,p]
}
fun movePhilosopherAt(s:State): one Philosopher{
	(s = last or not canMove[s]) => none
	else s.owned in next[s].owned => (next[s].owned-s.owned)[Fork]
    		else (s.owned - next[s].owned)[Fork] 
}
fun numberOfMoves(p:Philosopher):Int{
	sum s:State | #(p&movePhilosopherAt[s])
}
fact strongFairExecution{
	all disj p,q:Philosopher | numberOfMoves[p] = numberOfMoves[q]
--	all p:Philosopher | numberOfMoves[p]>=3
}

-- The number of State must be an kN+1,
-- where N is the number of forks and k is a natural number.
assert noDeadLock{
	all s:State | canMove[s]
}
check noDeadLock for exactly 3 Fork, 3 Philosopher,  16 State
