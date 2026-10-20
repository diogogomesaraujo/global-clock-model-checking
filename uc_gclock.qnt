// Model Checking a real-world and ideal GClock in the UC framework.

// Crossing with Confidence: Formal Analysis and
// Model Checking of Blockchain Bridges GClock

// Functionality 5: G-Clock[P]
//
// Init()
// 1:  r ← 0; Reg ← ∅; Done[∗] ← 0
//
// Psid.Reg()                      // any sid
// 2:  Reg ← Reg ∪ {Psid}
// 3:  if Psid ∉ Reg then
// 4:      Done[Psid] ← 0
// 5:  return ok
//
// Psid.Round()                    // any sid
// 6:  return r
//
// Sim.Round()
// 7:  return r
//
// Psid.OK()                       // any sid
// 8:  if Psid ∉ Reg then return ⊥
// 9:  Done[Psid] ← 1
// 10: flag ← 1
// 11: for P'sid' ∈ Reg \ C do
// 12:     if Done[P'sid'] = 0 then
// 13:         flag ← 0
// 14: if flag = 1 then
// 15:     r ← r + 1
// 16:     for P'sid' ∈ Reg \ C do
// 17:         Done[P'sid'] ← 0
// 18:     Sim(Psid.OK)
// 19: return ok

// Universally Composable Synchronous Computation FClock

// Functionality F_clock(P)
//
// Initialize for each p_i ∈ P a bit d_i := 0.
//
// – Upon receiving message (RoundOK) from party p_i:
//       set d_i := 1.
//       If for all p_j ∈ H : d_j = 1, then
//           reset d_j := 0 for all p_j ∈ P.
//       In any case, send (switch, p_i) to A.^a
//
// – Upon receiving (RequestRound) from p_i:
//       send d_i to p_i.
//
// – Upon receiving (corrupt, p_i) from A:
//       set H := H ∪ {p_i}.
//
// ^a The adversary is notified in each such call to allow attacks
//   at any point in time.

// References:
// - UC rules: https://swayam-padhy.gitbook.io/
// - GClock:   https://eprint.iacr.org/2026/292.pdf,
//             https://eprint.iacr.org/2011/310.pdf
// - Quint:    https://quint.sh/quint-cheatsheet.pdf

module utils {
    type Round = int

    type P_Sid = int

    type Sid = A | Z | P(P_Sid) | G_Clock

    type Flag = bool

    pure def One = true

    pure def Zero = false
}

module uc {
    import utils.*

    type Message[msg] = { sid : Sid, message : msg }

    type ITM[in, out, in_msg, out_msg] = {
        sid                : Sid,
        input              : List[in],
        output             : List[out],
        incomming_messages : List[Message[in_msg]],
        outgoing_messages  : List[Message[out_msg]]
    }
}

module rw_clock {
    import utils.*
    import uc.*
    import rw_environment 
    as environment

    type Input = Reg               ({ p_sid : P_Sid }) // in the paper Psid.Reg()
               | PartyRoundRequest ({ p_sid : P_Sid }) // in the paper Psid.Round()
               | RoundOk           ({ p_sid : P_Sid }) // in the paper Psid.OK()

    type Output = ()

    type Incoming = AdversaryRoundRequest ({ sid : Sid })      // in the paper Sim.Round() but adapted to the real world model
                   | Corrupt               ({ p_sid : P_Sid }) // note: modelling corruptions like Universally Composable Synchronous Computation instead

    type Outgoing = AdversaryRoundResponse ({ round : Round }) // in the paper r
                  | AdversaryOk            ({ p_sid : P_Sid }) // in the paper Sim(Psid.OK)

    type ClockITM = ITM[Input, Output, Incoming, Outgoing]

    type ClockState = {
        itm                : ClockITM,
        current_round      : Round,        // in the paper r
        registered_parties : Set[P_Sid],   // in the paper Reg
        corrupted_parties  : Set[P_Sid],   // in the paper C
        done               : P_Sid -> Flag // in the paper Done
    }
    
    // Action called by the clock when receiving a Reg request from Z.
    // It registers the party with sid P_Sid and, if it was not previously
    // registered it sets done[P_Sid] to 0.
    // Finally it puts an Ok message in Z's output-tape.
    action Register(GClock, P_Sid, Z) = {
        if (not(GClock.registered_parties.contains(P_Sid))) all {
            GClock' = GClock.with( "registered_parties"
                            , GClock.registered_parties.union(Set(P_Sid))),
            Z' = Z.with("itm", Z.itm.with( "output"
                                          , Z.itm.output.append(environment::Ok({ p_sid : P_Sid }))))
        }
        else all {
            GClock' = GClock.with("done" , GClock.done.put(P_Sid, Zero))
                          .with("registered_parties"
                               , GClock.registered_parties.union(Set(P_Sid))),
            Z' = Z.with("itm", Z.itm.with( "output"
                                         , Z.itm.output.append(environment::Ok({ p_sid : P_Sid }))))
        }
    }
}

module rw_adversary {
    import utils.*
    import uc.*

    type Input = Corrupt ({ p_sid : P_Sid })

    type Output = ()

    type Incoming = RoundResponse ({ round : Round })
                   | Ok ({ p_sid : P_Sid })

    type Outgoing = RoundRequest ({ sid : Sid })

    type AdversaryITM = ITM[Input, Output, Incoming, Outgoing]

    type AdversaryState = { 
        itm               : AdversaryITM,
        parties_that_oked : Set[P_Sid],
        corrupted_parties : Set[P_Sid]
    }
}

module rw_environment {
    import utils.*
    import uc.*

    type Input = ()

    type Output = Corrupted          ({ p_sid : P_Sid })
                | Ok                 ({ p_sid : P_Sid }) // in the paper ok
                | PartyRoundResponse ({ round: Round })  // in the paper r
                | Failed             ({ p_sid : P_Sid }) // in the paper ⊥

    type Incoming = ()

    type Outgoing = ()

    type EnvironmentITM = ITM[Input, Output, Incoming, Outgoing]

    type EnvironmentState = {
        itm : EnvironmentITM,
    }
}

module rw_party {
    import utils.*
    import uc.*

    type Input = RoundResponse ({ round : Round }) // in the paper Psid.Round()
               | Ok                                // in the paper Psid.OK()
               | Failed        ({ p_sid : P_Sid }) // in the paper ⊥

    type Output = ()

    type Incoming = ()

    type Outgoing = ()

    type PartyITM = ITM[Input, Output, Incoming, Outgoing]

    type PartyState = {
        itm : PartyITM,
    }
}

module rw {
    // The real-life model for executing protocol P with environment Z
    // consists of a system of interacting ITMs (Interactive Turing Machines).

    // 1. Initial ITM:
    // The environment Z is the initial ITM and has a fixed ID.

    // 2. Control Function:

    // Environment Z:
    // - Can activate a single instance of adversary A.
    // - Can activate multiple instances of protocol P.
    // - All instances of A and P share the same SID.
    // - Can write to the input tapes of the activated ITMs.

    // Adversary A:
    // - Can write to the incoming communication tapes of all protocol parties.
    // - Can write to the subroutine output tape of environment Z.

    // Other ITMs:
    // - Can write to the incoming communication tape of adversary A.
    // - Can invoke new ITMs.
    // - Can write to the subroutine output tape of their invoker.
    // - Can write to the input tapes of their subroutines.

    // 3. Modeling Corruptions:
    // The adversary A can corrupt an ITM M by writing a "corrupt"
    // message to M's incoming communication tape.

    // Once M receives the corruption request:
    // - M writes "corrupted" to the subroutine output tape of Z.
    // - During every subsequent activation, M sends its entire state to A.
    // - A assumes all write privileges previously held by M.
    // - M effectively operates under the control of A.
    
    import utils.*
}