// We are working methodically,
// by stating the signatures, 
// and sticking to our strategy that all transactions
// are either initial or terminal, meaning
// that securities are created and destroyed during every transaction.
open util/graph[Tx]

abstract sig Tx {
    parent :  lone Tx,
}

sig Stakeholder {
    portfolio : set Security
}

sig Security {
    shares : Int,
    owner : Stakeholder,
    initial : Tx,
    terminal : lone Tx
}

// I am getting spurious Securities that are not referreed to by any Tx.

pred validSecurity[s : Security] {

    s.initial in Issuance implies {
        (Issuance <: s.initial).security = s
    }

    s.initial in PartialCancellation implies {
        (PartialCancellation <: s.initial).balance = s
    }

    s.initial in Transfer implies {
        (Transfer <: s.initial).result = s
    }

    s.initial in PartialTransfer implies {
        ((PartialTransfer <: s.initial).result = s)
        or ((PartialTransfer <: s.initial).balance = s)
    }

    some s.terminal and s.terminal in Cancellation implies {
        (Cancellation <: s.terminal).security = s
    }

    some s.terminal and s.terminal in PartialCancellation implies {
        (PartialCancellation <: s.terminal).security = s
    }

    some s.terminal and s.terminal in Transfer implies {
        (Transfer <: s.terminal).security = s
    }

    some s.terminal and s.terminal in PartialTransfer implies {
        (PartialTransfer <: s.terminal).security = s
    }

}

sig Issuance extends Tx {
    security : Security,
    shares : Int,
    to : Stakeholder
}
sig Cancellation extends Tx {
    security : Security
}

sig PartialCancellation extends Tx {
    security : Security,
    balance : Security - security,
    shares : Int
}

sig Transfer extends Tx {
    security : Security,
    result : Security - security,
    to : Stakeholder
}

sig PartialTransfer extends Tx {
    security : Security,
    balance : Security - security,
    result : Security - security - balance,
    to : Stakeholder,
    shares : Int
}

fact {
    all s : Security {
        s.initial != s.terminal
    }
}

// Always aim for a check a property instead of stating a fact.
// Because sometimes the signatures and existing facts
// themselves are sufficient to verify the property.


check {
    all p : PartialTransfer {
        disj [p.result, p.balance, p.security]
    }
}

check {
    all p : PartialCancellation {
        disj [p.balance, p.security]
    }
}

check {
    all t : Transfer {
        disj [t.result, t.security]
    }
}

fact {
    no tx : Tx {
        tx in tx.^parent
    }
}

// This is trivial:
// 
// check {
//     all c : Cancellation {
//         disj [c.security]
//     }
// }
// 
// check {
//     all i : Issuance {
//         disj [i.security]
//     }
// }

// Now we will characterize valid transactions.
// Then we will ask the model finder to find instances
// that satisfy the characterization.

pred issuanceValid[i : Issuance] {
    i.security.initial = i
    i.security.shares = i.shares
    i.security.owner = i.to
    i.security.terminal != i
    pos[i.shares]

    // parent
    no i.security.initial.parent
}

pred cancellationValid[c : Cancellation] {
    c.security.terminal = c

    c.parent = c.security.initial
}

pred partialCancellationValid[pc : PartialCancellation] {
    pc.security.terminal = pc
    pc.balance.initial = pc
    pc.balance.owner = pc.security.owner
    eq[pc.balance.shares, sub[pc.security.shares, pc.shares]]

    pc.parent = pc.security.initial
}

pred transferValid[t : Transfer] {
    t.security.terminal = t
    t.result.initial = t
    t.result.shares = t.security.shares

    t.security.owner != t.to
    t.result.owner = t.to

    t.parent = t.security.initial
}

pred partialTransferValid[pt : PartialTransfer] {
    pt.balance.owner = pt.security.owner
    pt.result.owner = pt.to
    pt.to != pt.security.owner

    pt.security.terminal = pt
    pt.balance.initial = pt
    pt.result.initial = pt

    eq[pt.balance.shares, sub[pt.security.shares, pt.shares]]
    eq[pt.result.shares, pt.shares]

    pt.parent = pt.security.initial
}

pred validTx[tx : Tx] {
    tx in Issuance implies issuanceValid[tx]
    tx in Cancellation implies cancellationValid[tx]
    tx in PartialCancellation implies partialCancellationValid[tx]
    tx in Transfer implies transferValid[tx]
    tx in PartialTransfer implies partialTransferValid[tx]
}

fact validAllTx {
    all tx : Tx {
        validTx[tx]
    }
}

fact validAllSecurity {
    all s : Security {
        validSecurity[s]
    }
}

fact {
    all sh : Stakeholder {
        some sh.portfolio
    }
}

run {
    tree[parent]
} for 5