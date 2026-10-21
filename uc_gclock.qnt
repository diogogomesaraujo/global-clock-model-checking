// Model Checking a real-world and ideal GClock in the UC framework.

// Prove there exists π, A, Z s.t. forall S : EXEC_{π,A,Z} ≉ EXEC_{GClock,S,Z}

// Possible executions: 
// - a real-world model where honest parties can leave the protocol
// - a real-world model that can't guarantee that parties register at exactly
// the same time instance (execution may lag behind in some).
// - a real-world model with bounded-drift clocks (such as NTP)
// - one where messages are delivered asynchronously and can have delay.

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

    type Sid = S | Z | P(P_Sid) | G_Clock

    type Flag = bool

    type Pointer = int // points to the element it will evaluate (not the one it has already evaluated) 

    pure def One = true

    pure def Zero = false

    pure def InvalidP_Sid = -1

    pure def FirstRound = 0

    pure def NotPointing = 0
}

// UC Framework
// ^^^^^^^^^^^^

module uc {
    import utils.*

    type ITM[in, out, in_msg, out_msg] = {
        sid                : Sid,
        input              : List[in],
        output             : List[out],
        incoming_messages : List[in_msg],
        outgoing_messages  : List[out_msg],
        input_pointer      : Pointer,
        output_pointer     : Pointer,
        incoming_pointer  : Pointer,
        outgoing_pointer   : Pointer
    }

    pure def ItmInit(sid : Sid) : ITM = {
        sid                : sid,
        input              : [],
        output             : [],
        incoming_messages : [],
        outgoing_messages  : [],
        input_pointer      : NotPointing,
        output_pointer     : NotPointing,
        incoming_pointer  : NotPointing,
        outgoing_pointer   : NotPointing,
    }

    pure def AddInput(itm : ITM[a, b, c, d], msg : a) : ITM[a, b, c, d] = {
        itm.with("input", itm.input.append(msg))
    }

    pure def AddOutput(itm : ITM[a, b, c, d], msg : b) : ITM[a, b, c, d] = {
        itm.with("output", itm.output.append(msg))
    }

    pure def AddIncoming(itm : ITM[a, b, c, d], msg : c) : ITM[a, b, c, d] = {
        itm.with("incoming_messages", itm.incoming_messages.append(msg))
    }

    pure def AddOutgoing(itm : ITM[a, b, c, d], msg : d) : ITM[a, b, c, d] = {
        itm.with("outgoing_messages", itm.outgoing_messages.append(msg))
    }
}

// -----------------------------------------------------------------

// GClock
// ^^^^^^

module iw_clock {
    import utils.*
    import uc.*

    type Input = Reg               ({ p_sid : P_Sid }) // in the paper Psid.Reg()
               | PartyRoundRequest ({ p_sid : P_Sid }) // in the paper Psid.Round()
               | RoundOk           ({ p_sid : P_Sid }) // in the paper Psid.OK()

    type Output = ()

    type Incoming = SimulatorRoundRequest // in the paper Sim.Round() but adapted to the real world model
                   | Corrupt              ({ p_sid : P_Sid }) // note: modelling corruptions like Universally Composable Synchronous Computation instead

    type Outgoing = SimulatorRoundResponse ({ round : Round }) // in the paper r
                  | SimulatorOk            ({ p_sid : P_Sid }) // in the paper Sim(Psid.OK)

    type ClockITM = ITM[Input, Output, Incoming, Outgoing]

    type ClockState = {
        itm                : ClockITM,
        current_round      : Round,        // in the paper r
        registered_parties : Set[P_Sid],   // in the paper Reg
        corrupted_parties  : Set[P_Sid],   // in the paper C
        done               : P_Sid -> Flag // in the paper Done
    }
}

module iw_clock_actions {
    import utils.*
    import uc.*

    import iw_clock     as clock
    import iw_party     as party
    import iw_simulator as simulator

    // Action called by Z.
    // It initializes the G-Clock's state.
    action Init(GClock) = {
        GClock' = {
            itm                : ItmInit(G_Clock),
            current_round      : FirstRound,
            registered_parties : Set(),
            corrupted_parties  : Set(),
            done               : Map()
        }
    }

    // Action called by the clock when receiving a Reg request from P on the 
    // input tape.
    // It registers the party with sid P_Sid and, if it was not previously
    // registered it sets done[P_Sid] to 0.
    // Finally it puts an Ok message in P's output-tape.
    action Register(GClock, P) = {
        if (GClock.registered_parties.contains(party::p_sid(P))) all {
            GClock' = GClock.with( "registered_parties"
                                 , GClock.registered_parties.union(Set(party::p_sid(P)))),
            P' = P.with("itm", AddOutput(P.itm, party::Ok))
        }
        else all {
            GClock' = GClock.with( "done" 
                                 , GClock.done.put(party::p_sid(P), Zero))
                            .with( "registered_parties"
                                 , GClock.registered_parties.union(Set(party::p_sid(P)))),
            P' = P.with("itm", AddOutput(P.itm, party::Ok))
        }
    }

    // Action called by the clock when receiving a PartyRoundRequest request 
    // from P on the input tape.
    // Finally it puts a RoundResponse message in P's output-tape.
    action PartyRound(GClock, P) = {
        P' = P.with( "itm"
                   , AddOutput(P.itm, party::RoundResponse({ round : GClock.current_round })))
    }

    // Action called by the clock when receiving a Sim.Round() request 
    // from S on the incoming messages tape.
    // Finally it puts a RoundResponse message in S's incoming messages tape.
    action SimulatorRound(GClock, S) = {
        S' = S.with( "itm"
                   , AddIncoming(S.itm, simulator::RoundResponse({ round : GClock.current_round })))
    }

    action Ok(GClock, P, S) = {
        if (not(GClock.registered_parties.contains(party::p_sid(P)))) all {
            P' = P.with( "itm"
                        , AddOutput(P.itm, party::Failed)),
            S' = S,
            GClock' = GClock
        } else all { 
            if (not((GClock.registered_parties.exclude(GClock.corrupted_parties))
                            .exists(sid => GClock.done.put(party::p_sid(P), One).get(sid) == Zero)))
                GClock' = GClock.with( "done"
                                     , GClock.done.keys().mapBy(k => 
                                            if(GClock.registered_parties
                                                    .exclude(GClock.corrupted_parties)
                                                    .contains(k)) Zero
                                            else GClock.done.get(k)) )
                                                     .with( "current_round"
                                                          , GClock.current_round + 1 )
            else GClock' = GClock.with( "done"
                                      , GClock.done.put(party::p_sid(P), One) ),
            S' = S.with( "itm"
                       , AddIncoming(S.itm, simulator::Ok({ p_sid : party::p_sid(P) }))),
            P' = P.with( "itm"
                        , AddOutput(P.itm, party::Ok))
        }
    }
}

// -----------------------------------------------------------------

// Simulator
// ^^^^^^^^^

module iw_simulator {
    import utils.*
    import uc.*

    type Input = Corrupt ({ p_sid : P_Sid })

    type Output = ()

    type Incoming = RoundResponse ({ round : Round })
                   | Ok ({ p_sid : P_Sid })

    type Outgoing = RoundRequest ({ sid : Sid })

    type SimulatorITM = ITM[Input, Output, Incoming, Outgoing]

    type SimulatorState = { 
        itm               : SimulatorITM,
        parties_that_oked : Set[P_Sid],
        corrupted_parties : Set[P_Sid]
    }
}

module iw_simulator_actions {
    import uc.*
    
    import iw_clock as clock
    import utils    as utils

    // Action called by Z.
    // It initializes S's state.
    action Init(S) = {
        S' = {
            itm               : ItmInit(utils::S),
            parties_that_oked : Set(), // oked the current round
            corrupted_parties : Set(),
        }
    }

    action Round(GClock) = {
        GClock' = GClock.with( "itm"
                   , AddIncoming(GClock.itm, clock::SimulatorRoundRequest))
    }
}

// -----------------------------------------------------------------

// Environment
// ^^^^^^^^^^^

module iw_environment {
    import utils.*
    import uc.*

    type Input = ()

    type Output = Corrupted          ({ p_sid : P_Sid })
                | RegisterOk         ({ p_sid : P_Sid }) // in the paper ok
                | RoundOk            ({ p_sid : P_Sid }) // in the paper ok
                | PartyRound         ({ p_sid : P_Sid
                                      , round : Round }) // in the paper r
                | Failed             ({ p_sid : P_Sid }) // in the paper ⊥

    type Incoming = ()

    type Outgoing = ()

    type EnvironmentITM = ITM[Input, Output, Incoming, Outgoing]

    type EnvironmentState = {
        itm : EnvironmentITM,
    }
}

module iw_environment_actions {
    import utils
    import uc.*

    import iw_environment as environment

    // Action called by the model checker.
    // It initializes Z's state.
    action Init(Z) = {
        Z' = {
            itm : ItmInit(utils::Z),
        }
    }
}

// -----------------------------------------------------------------

// Party
// ^^^^^

module iw_party {
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
            | _        => InvalidP_Sid
        }
    }
}

module iw_party_actions {
    import uc.*
    import utils

    import iw_party       as party
    import iw_clock       as clock
    import iw_environment as environment

    // Action called by Z.
    // It initializes P's state.
    action Init(P, P_Sid) = {
        P' = {
            itm : ItmInit(utils::P(P_Sid)),
        }
    }

    // Action called by the party when receiving Reg from Z on
    // the input-tape.
    // Finally it puts an Reg message in the G-Clock's output-tape.
    action Register(P, GClock, Z) = {
        GClock' = GClock.with( "itm"
                             , AddInput(GClock.itm, clock::Reg({ p_sid : party::p_sid(P) })))
    }

    action RegisterResponse(P, Z, response) = {
        Z' = Z.with( "itm"
                   , AddOutput( Z.itm
                              , match response {
                                    | Ok     => environment::RegisterOk({ p_sid : party::p_sid(P) })
                                    | Failed => environment::Failed({ p_sid : party::p_sid(P) })
                                    | _      => environment::Failed({ p_sid : party::p_sid(P) })
                                }))
    }

    action Round(GClock, P) = {
        GClock' = GClock.with( "itm"
                             , AddInput( GClock.itm
                                        , clock::PartyRoundRequest({ p_sid : party::p_sid(P) })))
    }

    action RoundResponse(P, Z, round) = {
        Z' = Z.with( "itm"
                   , AddOutput(Z.itm, environment::PartyRound({ p_sid : party::p_sid(P)
                                                              , round : round })))
    }

    action Ok(GClock, P) = {
        GClock' = GClock.with( "itm"
                             , AddInput(GClock.itm, clock::RoundOk({ p_sid : party::p_sid(P) })))
    }

    action OkResponse(P, Z, response) = {
        Z' = Z.with( "itm"
                   , AddOutput( Z.itm
                              , match response {
                                    | Ok     => environment::RoundOk({ p_sid : party::p_sid(P) })
                                    | Failed => environment::Failed({ p_sid : party::p_sid(P) })
                                    | _      => environment::Failed({ p_sid : party::p_sid(P) })
                                }))
    }
}

// -----------------------------------------------------------------

// Ideal-world Model
// ^^^^^^^^^^^^^^^^

module iw {    
    import utils.*
}

// -----------------------------------------------------------------

// Real-world Model
// ^^^^^^^^^^^^^^^^

module rw {    
    import utils.*
}