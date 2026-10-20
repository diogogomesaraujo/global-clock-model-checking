// Model Checking a real-world and ideal GClock in the UC framework.

// References:
// - UC rules: https://swayam-padhy.gitbook.io/
// - GClock:   https://eprint.iacr.org/2026/292.pdf,
//             https://eprint.iacr.org/2011/310.pdf
// - Quint:    https://quint.sh/quint-cheatsheet.pdf

// -----------------------------------------------------------------

// Utils
// ^^^^^

module utils {
    type Round = int

    type P_Sid = int

    type Sid = A | Z | P(P_Sid) | G_Clock

    type Flag = bool

    pure def One = true

    pure def Zero = false

    pure def InvalidP_Sid = -1

    pure def FirstRound = 0
}

// UC Framework
// ^^^^^^^^^^^^

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

    pure def ItmInit(sid : Sid) : ITM = {
        sid                : sid,
        input              : [],
        output             : [],
        incomming_messages : [],
        outgoing_messages  : []
    }
}

// -----------------------------------------------------------------

// GClock
// ^^^^^^

module rw_clock {
    import utils.*
    import uc.*

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
}

module rw_clock_actions {
    import utils.*
    import uc.*

    import rw_clock as clock
    import rw_party as party

    action Init(GClock) = {
        GClock' = {
            itm                : ItmInit(G_Clock),
            current_round      : FirstRound,
            registered_parties : Set(),
            corrupted_parties  : Set(),
            done               : Map()
        }
    }

    // Action called by the clock when receiving a Reg request from P.
    // It registers the party with sid P_Sid and, if it was not previously
    // registered it sets done[P_Sid] to 0.
    // Finally it puts an Ok message in P's output-tape.
    action Register(GClock, P) = {
        if (GClock.registered_parties.contains(party::p_sid(P))) all {
            GClock' = GClock.with( "registered_parties"
                                 , GClock.registered_parties.union(Set(party::p_sid(P)))),
            P' = P.with("itm", P.itm.with( "output"
                                          , P.itm.output.append(party::Ok)))
        }
        else all {
            GClock' = GClock.with( "done" 
                                 , GClock.done.put(party::p_sid(P), Zero))
                            .with( "registered_parties"
                                 , GClock.registered_parties.union(Set(party::p_sid(P)))),
            P' = P.with("itm", P.itm.with( "output"
                                         , P.itm.output.append(party::Ok)))
        }
    }
}

// -----------------------------------------------------------------

// Adversary
// ^^^^^^^^^

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

module rw_adversary_actions {
    import uc.*
    import utils.*
    
    import utils as utils

    action Init(A) = {
        A' = {
            itm               : ItmInit(utils::A),
            parties_that_oked : Set(),
            corrupted_parties : Set(),
        }
    }
}

// -----------------------------------------------------------------

// Environment
// ^^^^^^^^^^^

module rw_environment {
    import utils.*
    import uc.*

    type Input = ()

    type Output = Corrupted          ({ p_sid : P_Sid })
                | Ok                 ({ p_sid : P_Sid }) // in the paper ok
                | PartyRoundResponse ({ round : Round }) // in the paper r
                | Failed             ({ p_sid : P_Sid }) // in the paper ⊥

    type Incoming = ()

    type Outgoing = ()

    type EnvironmentITM = ITM[Input, Output, Incoming, Outgoing]

    type EnvironmentState = {
        itm : EnvironmentITM,
    }
}

module rw_environment_actions {
    import utils
    import uc.*

    import rw_environment as environment

    action Init(Z) = {
        Z' = {
            itm : ItmInit(utils::Z),
        }
    }
}

// -----------------------------------------------------------------

// Party
// ^^^^^

module rw_party {
    import utils.*
    import uc.*

    type Input = Reg          // in the paper Psid.Reg()
               | RoundRequest // in the paper Psid.Round()
               | RoundOk      // in the paper Psid.OK()

    type Output = RoundResponse ({ round : Round }) // in the paper Psid.Round()
               | Ok                                 // in the paper Psid.OK()
               | Failed                             // in the paper ⊥

    type Incoming = ()

    type Outgoing = ()

    type PartyITM = ITM[Input, Output, Incoming, Outgoing]

    type PartyState = {
        itm : PartyITM,
    }

    pure def p_sid(P : PartyState) : P_Sid = {
        match (P.itm.sid) {
            | P(p_sid) => p_sid
            | A        => InvalidP_Sid
            | Z        => InvalidP_Sid
            | G_Clock  => InvalidP_Sid
        }
    }
}

module rw_party_actions {
    import uc.*
    import utils

    import rw_party       as party
    import rw_clock       as clock
    import rw_environment as environment

    action Init(P, P_Sid) = {
        P' = {
            itm : ItmInit(utils::P(P_Sid)),
        }
    }

    // Action called by the environment.
    // Finally it puts an Ok message in Z's output-tape.
    action Register(P, GClock, Z) = all {
        GClock' = GClock.with( "itm"
                             , GClock.itm.with( "input"
                                              , GClock.itm.input.append(clock::Reg ({ 
                                                                            p_sid : party::p_sid(P) 
                                                                        })))),
        Z' = Z.with( "itm"
                   , Z.itm.with( "output"
                               , Z.itm.output.append(environment::Ok({ p_sid : party::p_sid(P) }))))
    }
}

// -----------------------------------------------------------------

// Real-world Model
// ^^^^^^^^^^^^^^^^

module rw {    
    import utils.*
}