open util/ordering[Security]
open util/ordering[Transaction]

open util/graph[Security]
open util/graph[Transaction]

sig Stakeholder {
    portfolio : set Security
}

fact {
	portfolio = ~owner
}

sig Security {
    shares : Int,
    source : one Transaction,
    use : lone Transaction,
    parent : lone Security,
    owner : Stakeholder
}

abstract sig Transaction {
    shares : Int,
    input : lone Security,
    output : lone Security,
    balance : lone Security,
    parent : lone Transaction
} {
    pos[shares]
}

fact {
    use = ~input
}

fact {
    source = ~(output + balance)
}

sig Issuance extends Transaction {
    to : Stakeholder
} {
    no input
    no balance
    one output
    no (Transaction <: parent)
}

sig Cancellation extends Transaction {} {
    no output
    lone balance
    one input
    one (Transaction <: parent)
}

sig Transfer extends Transaction {
    from : Stakeholder,
    to : Stakeholder - from
} {
    one input
    one output
    lone balance
    one (Transaction <: parent)
}

fact {
    all iss : Issuance {
        eq[iss.output.shares, iss.shares]
        iss.output.source = iss
        iss.output.owner = iss.to
        iss.output in iss.to.portfolio
    }
}

fact {
    all can : Cancellation {
        lt[can.shares, can.input.shares] implies {
            // In this case, the transaction is partial.
            can.input.use = can
            can.balance.source = can
            eq[can.balance.shares, sub[can.input.shares, can.shares]]
            lt[can.input, can.balance]
            can.balance.owner = can.input.owner
            can.balance in can.input.owner.portfolio
            can.balance.parent = can.input
            can.parent = can.input.source
        } else {
            can.input.use = can
            eq[can.input.shares, can.shares]
            can.parent = can.input.source
            no can.balance            
        }
    }
}

fact {
    all xfer : Transfer {
        lt[xfer.shares, xfer.input.shares] implies {
            // In this case, the transaction is partial.
            xfer.input.use = xfer
            xfer.output.source = xfer
            xfer.balance.source = xfer
            eq[xfer.output.shares, xfer.shares]
            eq[xfer.balance.shares, sub[xfer.input.shares, xfer.shares]]
            lt[xfer.input, xfer.output]
            lt[xfer.input, xfer.balance]
            xfer.output.owner = xfer.to
            xfer.input.owner = xfer.from
            xfer.balance.owner = xfer.from
            xfer.from.portfolio = xfer.from.portfolio + xfer.balance
            xfer.to.portfolio = xfer.to.portfolio + xfer.output
            xfer.output.parent = xfer.input
            xfer.balance.parent = xfer.input
            xfer.parent = xfer.input.source
        } else {
            xfer.input.use = xfer
            xfer.output.source = xfer
            eq[xfer.output.shares, xfer.shares]
            eq[xfer.shares, xfer.input.shares]
            lt[xfer.input, xfer.output]
            xfer.output.owner = xfer.to
            xfer.input.owner = xfer.from            
            xfer.to.portfolio = xfer.to.portfolio + xfer.output
            xfer.output.parent = xfer.input
            no xfer.balance
            xfer.parent = xfer.input.source
        }
    }
}

pred orderingOfSecurities {
    all sec : Security {
        some sec.parent implies {
            lt[sec.parent, sec]
        }
    }
}

pred orderingOfTransactions {
    all tx : Transaction {
        some tx.parent implies {
            lt[tx.parent, tx]
        }
    }
}

fun lineage[sec : Security] : set Security {
    sec.*(Security <: parent)
}

fun lineage[tx : Transaction] : set Transaction {
    tx.*(Transaction <: parent)
}

fun depth[sec : Security] : Int {
    #lineage[sec]
}

fun aliveSecurities : set Security {
    { sec : Security | no sec.use }
}

fun deadSecurities : set Security {
    { sec : Security | some sec.use }
}

fun issuedShares : Int {
    sum iss : Issuance | iss.shares
}

fun cancelledShares : Int {
    sum can : Cancellation | can.shares
}

fun transferredShares : Int {
    sum xfer : Transfer | xfer.shares
}

fun aliveShares : Int {
    sum sec : aliveSecurities | sec.shares
}

fun deadShares : Int {
    sum sec : deadSecurities | sec.shares
}

securitiesAreForest : check {
    orderingOfSecurities => forest[~(Security <: parent)]
}

transactionsAreForest : check {
    orderingOfTransactions => forest[~(Transaction <: parent)]
}

cancelledSharesAlwaysLessThanIssued : check {
    lte[cancelledShares, issuedShares]
} for 3

nonNegativityOfIssuedShares : check {
    nonneg[issuedShares]
} for 3

nonNegativityOfCancelledShares : check {
    nonneg[cancelledShares]
} for 3

aliveLessThanIssued : check {
    lte[aliveShares, issuedShares]
} for 3

noOverlap : check {
    all o1, o2 : Stakeholder {
        some o1.portfolio & o2.portfolio implies o1 = o2
    }
}

pred superTransferral {
    lte[issuedShares, transferredShares]
}

pred long {
    some sec : Security | depth[sec] > 3
}

check {
    no s : Security | neg[s.shares]
}

fun portfolioShares[stakeholder : Stakeholder] : Int {
    sum sec : stakeholder.portfolio | (sec in aliveSecurities implies sec.shares else 0)
}

fun portfolioSharesAll : Int {
    sum stakeholder : Stakeholder | portfolioShares[stakeholder]
}

check {
    eq[aliveShares, portfolioSharesAll]
}

run superTransferral for 3

run long for 5

bigExample : run {
    #Stakeholder = 3
	#Issuance = 1
	#Transfer = 3
	#Cancellation = 1
} for 5

check {
    all s : Security {
        some i : Issuance | i in lineage[s].source
    }
}

check {
    all t : Transaction {
        some i : Issuance | i in lineage[t]
    }
}

fact {
    all s : Security {
        s in Issuance.output implies no s.parent
    }
}

run {
    some sec : Security | depth[sec] > 3
} for 5