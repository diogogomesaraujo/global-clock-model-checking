// Functionality 5: G-Clock[P]
module real_world {
    type Sid = int // party identifier

    var r:     int         // round
    var reg :  Set[Sid]    // registered parties
    var done : Sid -> bool // parties that intend to advance to the next round
    var c :    Set[Sid]    // corrupted parties

    pure val zero = false
    pure val one  = true

    // Init()
    //   1: r ← 0
    //   2: Reg ← ∅
    //   3: Done[*] ← 0
    action Init = all {
        r'    = 0,
        reg'  = Set(),
        done' = Map(),
        c'    = Set()
    }

    // Psid.Reg()   // invoked by any sid
    //   1: Reg ← Reg ∪ {Psid}
    //   2: if Psid ∉ Reg then
    //   3:     Done[Psid] ← 0
    //   4:     return ok
    action Reg(P_sid) = all {
        reg' = reg.union(Set(P_sid)),
        if (not(reg.contains(P_sid))) 
             done' = done.put(P_sid, zero)
        else done' = done,
    }

    // Psid.Round()  // invoked by any sid
    //   1: return r
    //
    // Sim.Round()
    //   1: return r
    pure def Round() : int = r

    temporal NextRound() : int = next(r)

    // Psid.OK()   // invoked by any sid
    //   1: if Psid ∉ Reg then
    //   2:     return ⊥
    //   3: Done[Psid] ← 1
    //   4: flag ← 1
    //   5: for P'sid' ∈ Reg \ C do
    //   6:     if Done[P'sid'] = 0 then
    //   7:         flag ← 0
    //   8: if flag = 1 then
    //   9:     r ← r + 1
    //  10: for P'sid' ∈ Reg \ C do
    //  11:     Done[P'sid'] ← 0
    //  12: Sim(Psid.OK)
    //  13: return ok
    //
    // disclamer: the flag is omitted because of model checking limitations.
    action Ok(P_sid) = all { 
        if (reg.contains(P_sid))
            all { 
                if (not((reg.exclude(c)).exists(sid => 
                        done.put(P_sid, one).get(sid) == zero)))
                    all {
                        done' = done.keys().mapBy(k => 
                            if ((reg.exclude(c)).contains(k)) zero 
                            else done.get(k)),
                        r' = r + 1
                    }
                else all {
                    done' = done.put(P_sid, one),
                    r' = r
                }
            }
        else all {
            r' = r,
            done' = done
        }, 
    }

    action Corrupt(P_sid) = all {
        c' = c.union(Set(P_sid))
    }

    // Example

    var count : int

    action init = all {
        Init,
        count' = 0
    }

    action step = any {
        // P_sid.Reg()
        all {
            Reg(count),
            count' = count + 1,
            
            // default
            r' = r,
            c' = c
        },

        // P_sid.Ok()
        all { 
            nondet sid = oneOf(0.to(count - 1))
            Ok(sid),

            //default
            reg'   = reg,
            count' = count,
            c'     = c
        },

        // P_sid corrupted
        all {
            nondet sid = oneOf(0.to(count - 1))
            Corrupt(sid),

            // default
            reg'   = reg,
            count' = count,
            r'     = r,
            done'  = done
        },

        // Idle

        all {
            c'     = c,
            reg'   = reg,
            count' = count,
            r'     = r,
            done'  = done
        }
    }

    // r incrementing implies that forall sid ∈ Reg / (C ∪ {sid'}), where sid'
    // is the id of the last honest party that has yet to declare its intent to 
    // continue to the next round, Done[sid] = 1.
    temporal prop_advance =
        (NextRound == Round + 1).implies(
            (reg.exclude(c)).forall(sid =>
                done.get(sid) == one
            )
        )
}