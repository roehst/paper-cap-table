open util/ordering[Date]
open util/graph[VestingTrigger]

fact {
	dag[children]
}

sig Date {}

sig Event {}

sig VestingTerm {
    conditions : disj set VestingCondition,
    authorizedShares : Int
}
sig VestingCondition {
    trigger : VestingTrigger,
    state : State,
    shares : Int
}

abstract sig VestingTrigger {
    state : State,
	children : set VestingTrigger
}

sig ExactDateTrigger extends VestingTrigger {
    exactDate : one Date
} {
	no children
}

sig ExactEventTrigger extends VestingTrigger {
    exactEvent : one Event
} { 
	no children
}

sig AndTrigger extends VestingTrigger {
	andOp1 : one VestingTrigger,
	andOp2 : one VestingTrigger - andOp1
} {
	children = andOp1 + andOp2
}

sig OrTrigger extends VestingTrigger {
	orOp1 : one VestingTrigger,
	orOp2 : one VestingTrigger - orOp1
} {
	children = orOp1 + orOp2
}

sig NotTrigger extends VestingTrigger {
    notOp : one VestingTrigger
} {
    children = notOp
}

// Eval under:
sig pastEvents in Event {}
one sig currentDate in Date {}

fact {
	all t : ExactDateTrigger {
		lte[t.exactDate, currentDate] iff t.state = Yes
	}
}

fact {
	all t : ExactEventTrigger {
		t.exactEvent in pastEvents iff t.state = Yes
	}
}

fact {
	all t : AndTrigger {
		t.state = Yes iff (t.andOp1.state = Yes and t.andOp2.state = Yes)
	}
}

fact {
	all t : OrTrigger {
		t.state = Yes iff (t.orOp1.state = Yes or t.orOp2.state = Yes)
	}
}

fact {
    all t : NotTrigger {
        t.state = Yes iff t.notOp.state = No
    }
}

enum State {
    Yes, No
}

fact {
    all t : VestingTerm {
        eq[t.authorizedShares, grantedShares[t]]
    }
}

fact {
    all t : VestingTerm | pos[t.authorizedShares]
}

fact {
    all c : VestingCondition | pos[c.shares]
}

fact {
    all t : VestingTerm {
        eq[t.authorizedShares, sum c : t.conditions | c.shares]
    }
}

fact {
    all c : VestingCondition {
        c.trigger.state = Yes iff c.state = Yes
    }
}

fun vestedShares[c : VestingCondition] : Int {
    c.state = Yes implies c.shares else 0
}

fun vestedShares[t : VestingTerm] : Int {
    sum c : t.conditions | vestedShares[c]
}

fun grantedShares[t : VestingTerm] : Int {
    sum c : t.conditions | c.shares
}

fun vestedConditions[t : VestingTerm] : set VestingCondition {
    { c : t.conditions | c.state = Yes }
}

check {
    all t : VestingTerm {
        gte[grantedShares[t], vestedShares[t]]
    }  
}

check {
    all t : VestingTerm {
        pos[grantedShares[t]]
    }  
}

check {
    all t : VestingTerm {
        nonneg[vestedShares[t]]
    }  
}

fact {
	all c : VestingCondition | some t : VestingTerm | c in t.conditions
	all t : VestingTrigger | some  c : VestingCondition | t = c.trigger
}

run { 
	Yes + No = ExactDateTrigger.state
	Yes + No = ExactEventTrigger.state
	some AndTrigger
	some OrTrigger
    one VestingTerm
} for 6

// Now the model can be linked to a 
// model very similar to the transaction tracing model,
// adding a transactions similar to an Exercise that outputs
// a new plan security with more exercised shares and the same vesting term






