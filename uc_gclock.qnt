// Model Checking a real-world clock constructions against the ideal functionality
// GClock in the UC framework.

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

module assumptions {
    pure val NumberOfParties = 10
}

module utils {
    type Round = int

    pure def FirstRound = 0

    // ^^^^^
    
    type P_Sid = int

    type Sid = S | Z | P(P_Sid) | G_Clock

    pure def InvalidP_Sid = -1

    // ^^^^^

    type Flag = bool

    pure def One = true

    pure def Zero = false

    // ^^^^^

    type Pointer = int // points to the element it will evaluate (not the one it has already evaluated) 

    pure def NotPointing = 0

    // ^^^^^

    type Option[a] = Some(a) | None

    // ^^^^^

    type Effects[a] = List[a]
}

// UC Framework
// ^^^^^^^^^^^^

module uc {
    import utils.*

    type ITM[in, out, in_msg] = {
        sid                : Sid,
        input              : List[in],
        output             : List[out],
        incoming_messages : List[in_msg],
        input_pointer      : Pointer,
        output_pointer     : Pointer,
        incoming_pointer  : Pointer,
    }

    type ItmEffect[in, out, in_msg] = UpdateInput(in)
                                    | UpdateOutput(out)
                                    | UpdateIncoming(in_msg)
                                    | IncrementInputPointer
                                    | IncrementOutputPointer
                                    | IncrementIncomingPointer

    pure def ItmInit(sid : Sid) : ITM = {
        sid               : sid,
        input             : [],
        output            : [],
        incoming_messages : [],
        input_pointer     : NotPointing,
        output_pointer    : NotPointing,
        incoming_pointer  : NotPointing,
    }

    pure def ApplyEffect(itm : ITM[a, b, c], effect : ItmEffect) : ITM[a, b, c] = {
        match (effect) {
            | UpdateInput(msg)         => AddInput(itm, msg)
            | UpdateOutput(msg)        => AddOutput(itm, msg)
            | UpdateIncoming(msg)      => AddIncoming(itm, msg)
            | IncrementInputPointer    => IncrInputPointer(itm)
            | IncrementOutputPointer   => IncrOutputPointer(itm)
            | IncrementIncomingPointer => IncrIncomingPointer(itm)
        }
    }

    pure def ApplyEffects(itm : ITM[a, b, c], effects : Effects[ItmEffect]) : ITM[a, b, c] = {
        effects.foldl(itm, (acc, e) => ApplyEffect(itm, e))
    }

    pure def AddInput(itm : ITM[a, b, c], msg : a) : ITM[a, b, c] = {
        itm.with("input", itm.input.append(msg))
    }

    pure def AddOutput(itm : ITM[a, b, c], msg : b) : ITM[a, b, c] = {
        itm.with("output", itm.output.append(msg))
    }

    pure def AddIncoming(itm : ITM[a, b, c], msg : c) : ITM[a, b, c] = {
        itm.with("incoming_messages", itm.incoming_messages.append(msg))
    }

    pure def ReadNew(tape : List[a], pointer : Pointer) : Option[a] = {
        if (length(tape)      == 0) None
        else if (length(tape) <= pointer) None
        else Some(tape[pointer])
    }

    pure def ReadNewInput(itm : ITM[a, b, c]) : Option[a] = {
        ReadNew(itm.input, itm.input_pointer)
    }

    pure def ReadNewOutput(itm : ITM[a, b, c]) : Option[b] = {
        ReadNew(itm.output, itm.output_pointer)
    }

    pure def ReadNewIncoming(itm : ITM[a, b, c]) : Option[c] = {
        ReadNew(itm.incoming_messages, itm.incoming_pointer)
    }

    pure def IncrInputPointer(itm : ITM[a, b, c]) : ITM[a, b, c] = {
        itm.with("input_pointer", itm.input_pointer + 1)
    }

    pure def IncrOutputPointer(itm : ITM[a, b, c]) : ITM[a, b, c] = {
        itm.with("output_pointer", itm.output_pointer + 1)
    }

    pure def IncrIncomingPointer(itm : ITM[a, b, c]) : ITM[a, b, c] = {
        itm.with("incoming_pointer", itm.incoming_pointer + 1)
    }
}

// -----------------------------------------------------------------

// GClock
// ^^^^^^

module iw_clock {
    import utils.*
    import uc as uc

    type Input = Reg               ({ p_sid : P_Sid }) // in the paper Psid.Reg()
               | PartyRoundRequest ({ p_sid : P_Sid }) // in the paper Psid.Round()
               | RoundOk           ({ p_sid : P_Sid }) // in the paper Psid.OK()

    type Output = ()

    type Incoming = SimulatorRoundRequest                     // in the paper Sim.Round() but adapted to the real world model
                   | Corrupt              ({ p_sid : P_Sid }) // note: modelling corruptions like Universally Composable Synchronous Computation instead

    type ClockITM = uc::ITM[Input, Output, Incoming]

    type ClockState = {
        itm                : ClockITM,
        current_round      : Round,        // in the paper r
        registered_parties : Set[P_Sid],   // in the paper Reg
        corrupted_parties  : Set[P_Sid],   // in the paper C
        done               : P_Sid -> Flag // in the paper Done
    }

    type Actions = RdInput | RdIncoming | RdOutput

    type ClockEffect = UpdateItm(uc::ItmEffect)
                     | IncrementRound
                     | UpdateRegistered(P_Sid)
                     | UpdateCorrupted(P_Sid)
                     | UpdateDone({ p_sid : P_Sid, flag : Flag})

    pure def ApplyEffect(state : ClockState, effect : ClockEffect) : ClockState = {
        match (effect) {
            | UpdateItm(e)            => state.with("itm", uc::ApplyEffect(state.itm, e))
            | UpdateRegistered(p_sid) => AddRegistered(state, p_sid)
            | UpdateCorrupted(p_sid)  => AddCorrupted(state, p_sid)
            | UpdateDone(d)           => AddDone(state, d.p_sid, d.flag)
            | IncrementRound          => IncrRound(state)
        }
    }

    pure def ApplyEffects(state : ClockState, effects : Effects[ClockEffect]) : ClockState = {
        effects.foldl(state, (acc, e) => ApplyEffect(state, e))
    }

    pure def AddRegistered(state : ClockState, p_sid : P_Sid) : ClockState = {
        state.with("registered_parties", state.registered_parties.union(Set(p_sid)))
    }

    pure def AddCorrupted(state : ClockState, p_sid : P_Sid) : ClockState = {
        state.with("corrupted_parties", state.corrupted_parties.union(Set(p_sid)))
    }

    pure def AddDone(state : ClockState, p_sid : P_Sid, flag : Flag) : ClockState = {
        state.with("done", state.done.put(p_sid, flag))
    }

    pure def IncrRound(state : ClockState) : ClockState = {
        state.with("current_round", state.current_round + 1)
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
    action Register(GClock, Parties, p_sid) = {
        if (GClock.registered_parties.contains(p_sid)) all {
            GClock' = GClock.with( "registered_parties"
                                 , GClock.registered_parties.union(Set(p_sid))),
            Parties' = Parties.put(p_sid, Parties.get(p_sid).with("itm", AddOutput(Parties.get(p_sid).itm, party::Ok)))
        }
        else all {
            GClock' = GClock.with( "done" 
                                 , GClock.done.put(p_sid, Zero))
                            .with( "registered_parties"
                                 , GClock.registered_parties.union(Set(p_sid))),
            Parties' = Parties.put(p_sid, Parties.get(p_sid).with("itm", AddOutput(Parties.get(p_sid).itm, party::Ok)))
        }
    }

    // Action called by the clock when receiving a PartyRoundRequest request 
    // from P on the input tape.
    // Finally it puts a RoundResponse message in P's output-tape.
    action PartyRound(GClock, Parties, p_sid) = {
        Parties' = Parties.put( p_sid
                               , Parties.get(p_sid).with( "itm"
                                                        , AddOutput( Parties.get(p_sid).itm
                                                                   , party::RoundResponse({ round : GClock.current_round }))))
    }

    // Action called by the clock when receiving a Sim.Round() request 
    // from S on the incoming messages tape.
    // Finally it puts a RoundResponse message in S's incoming messages tape.
    action SimulatorRound(GClock, S) = {
        S' = S.with( "itm"
                   , AddIncoming(S.itm, simulator::RoundResponse({ round : GClock.current_round })))
    }

    action Ok(GClock, Parties, p_sid, S) = {
        if (not(GClock.registered_parties.contains(p_sid))) all {
            Parties' = Parties.put(p_sid, Parties.get(p_sid).with( "itm"
                                                                 , AddOutput(Parties.get(p_sid).itm, party::Failed))),
            S' = S,
            GClock' = GClock
        } else all { 
            if (not((GClock.registered_parties.exclude(GClock.corrupted_parties))
                            .exists(sid => GClock.done.put(p_sid, One).get(sid) == Zero)))
                GClock' = GClock.with( "done"
                                     , GClock.done.keys().mapBy(k => 
                                            if(GClock.registered_parties
                                                    .exclude(GClock.corrupted_parties)
                                                    .contains(k)) Zero
                                            else GClock.done.get(k)) )
                                                     .with( "current_round"
                                                          , GClock.current_round + 1 )
            else GClock' = GClock.with( "done"
                                      , GClock.done.put(p_sid, One) ),
            S' = S.with( "itm"
                       , AddIncoming(S.itm, simulator::Ok({ p_sid : p_sid }))),
            Parties' = Parties.put(p_sid, Parties.get(p_sid).with( "itm"
                                                                 , AddOutput(Parties.get(p_sid).itm, party::Ok)))
        }
    }

//     action Step(GClock, Z, S, Parties) = {
//         nondet which = oneOf(Set(clock::RdInput, clock::RdIncoming, clock::RdOutput))
//         match (which) {
//             | clock::RdInput    => {
//                 match (ReadNew(GClock.itm.input, GClock.itm.input_pointer)) {
//                     Some(input_message) => {
//                         match (input_message) {
//                             | Reg(r)               => all {
//                                 Register(GClock, Parties, r.p_sid)
//                             }
//                             | PartyRoundRequest(r) => all {
//                                 PartyRound(GClock, Parties, r.p_sid)
//                             }
//                             | RoundOk(r)           => all {
//                                 Ok(GClock, Parties, r.p_sid, S)
//                             }
//                         }
//                     }
//                     None                => all {
//                         GClock'  = GClock,
//                         Z'       = Z,
//                         S'       = S,
//                         Parties' = Parties
//                     }
//                 }
//             }
//             | clock::RdIncoming => {

//             }
//             | clock::RdOutput   => {

//             }
//         }
//     }
}

// -----------------------------------------------------------------

// Simulator
// ^^^^^^^^^

module iw_simulator {
    import utils.*
    import uc.*

    type Input = ()

    type Output = ()

    type Incoming = RoundResponse ({ round : Round })
                   | Ok           ({ p_sid : P_Sid })


    type SimulatorITM = ITM[Input, Output, Incoming]

    type SimulatorState = { 
        itm               : SimulatorITM,
        parties_that_oked : Set[P_Sid],
        corrupted_parties : Set[P_Sid]
    }

    type Actions = Corrupt | RdIncoming | RdOutput

    type SimulatorEffect = UpdateItm(ItmEffect)
                         | UpdatedOked(P_Sid)
                         | UpdateCorrupted(P_Sid)
}

module iw_simulator_actions {
    import uc.*
    
    import iw_simulator as simulator
    import iw_clock     as clock
    import utils        as utils

    // Action called by Z.
    // It initializes S's state.
    action Init(S) = {
        S' = {
            itm               : ItmInit(utils::S), // for now here because we don't need to consider the machine before activation
            parties_that_oked : Set(),             // oked the current round
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

    type EnvironmentITM = ITM[Input, Output, Incoming]

    type EnvironmentState = {
        itm : EnvironmentITM,
    }

    type EnvironmentEffect = | UpdateItm(ItmEffect)
}

module iw_environment_actions {
    import utils
    import uc.*

    import iw_party       as party
    import iw_simulator   as simulator
    import iw_environment as environment

    // Action called by the model checker.
    // It initializes Z's state.
    action Init(Z) = all {
        Z' = {
            itm : ItmInit(utils::Z),
        },
    }
}

// -----------------------------------------------------------------

// Dummy Party
// ^^^^^^^^^^^

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

    type PartyITM = ITM[Input, Output, Incoming]

    type PartyState = {
        current_round : Round,
        itm           : PartyITM,
    }

    type Parties = P_Sid -> PartyState

    pure def p_sid(P : PartyState) : P_Sid = {
        match (P.itm.sid) {
            | P(p_sid) => p_sid
            | _        => InvalidP_Sid
        }
    }

    type Actions = ()

    type EnvironmentEffect = UpdateItm(ItmEffect)
                           | UpdateRound(Round)
}

module iw_party_actions {
    import uc.*
    import assumptions.*

    import utils

    import iw_party       as party
    import iw_clock       as clock
    import iw_environment as environment

    // Action called by Z.
    // It initializes P's state.
    action Init(Parties) = {
        Parties' = 1.to(NumberOfParties).mapBy(i => ({ itm : ItmInit(utils::P(i)), current_round : 0 }))
    }

    // Action called by the party when receiving Reg from Z on
    // the input-tape.
    // Finally it puts an Reg message in the G-Clock's output-tape.
    action Register(p_sid, GClock, Z) = {
        GClock' = GClock.with( "itm"
                             , AddInput(GClock.itm, clock::Reg({ p_sid : p_sid })))
    }

    action RegisterResponse(p_sid, Z, response) = {
        Z' = Z.with( "itm"
                   , AddOutput( Z.itm
                              , match response {
                                    | Ok     => environment::RegisterOk({ p_sid : p_sid })
                                    | Failed => environment::Failed({ p_sid : p_sid })
                                    | _      => environment::Failed({ p_sid : p_sid })
                                }))
    }

    action Round(GClock, p_sid) = {
        GClock' = GClock.with( "itm"
                             , AddInput( GClock.itm
                                        , clock::PartyRoundRequest({ p_sid : p_sid })))
    }

    action RoundResponse(p_sid, Z, round) = {
        Z' = Z.with( "itm"
                   , AddOutput(Z.itm, environment::PartyRound({ p_sid : p_sid
                                                              , round : round })))
    }

    action Ok(GClock, p_sid) = {
        GClock' = GClock.with( "itm"
                             , AddInput(GClock.itm, clock::RoundOk({ p_sid : p_sid })))
    }

    action OkResponse(p_sid, Z, response) = {
        Z' = Z.with( "itm"
                   , AddOutput( Z.itm
                              , match response {
                                    | Ok     => environment::RoundOk({ p_sid : p_sid })
                                    | Failed => environment::Failed({ p_sid : p_sid })
                                    | _      => environment::Failed({ p_sid : p_sid })
                                }))
    }
}

// -----------------------------------------------------------------

// Ideal-world Model
// ^^^^^^^^^^^^^^^^

module iw {    
    import uc as uc

    import utils as utils

    import iw_party_actions       as party_actions
    import iw_clock_actions       as clock_actions
    import iw_environment_actions as environment_actions
    import iw_simulator_actions   as simulator_actions

    import iw_clock       as clock
    import iw_simulator   as simulator
    import iw_environment as environment
    import iw_party       as party

    var Z       : environment::EnvironmentState
    var S       : simulator::SimulatorState
    var GClock  : clock::ClockState
    var Parties : party::Parties

    // all parties begin already activated by the environment. 
    // in the ideal world he assume all parties are registered before
    // they start interacting with the GClock. 
    action Init = all {
        environment_actions::Init(Z),
        simulator_actions::Init(S),
        clock_actions::Init(GClock),
        party_actions::Init(Parties)
    }
}

// -----------------------------------------------------------------

// Real-world Model
// ^^^^^^^^^^^^^^^^

module rw {    
    import utils.*
}