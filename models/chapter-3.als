sig Stakeholder {
    portfolio : set Security
}

sig Security {
    owner : one Stakeholder
}

pred invOwnerPortfolio { ~owner = portfolio }

pred overlap[s1, s2 : Stakeholder] {
    s1.portfolio & s2.portfolio != none
}

assert noSharedOwnership {
    no disj s1, s2 : Stakeholder | overlap[s1, s2]
}

check noSharedOwnership for 5

check noSharedOwnershipAlt {
    invOwnerPortfolio implies {
        no disj s1, s2 : Stakeholder | overlap[s1, s2]
    }
}

run {} for 5 but exactly 2 Stakeholder, 5 Security