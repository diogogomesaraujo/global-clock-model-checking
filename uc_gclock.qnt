// Model Checking G-Clock
// from: https://eprint.iacr.org/2026/292.pdf

// -----------------------------------------------------------------

// Utils
// ^^^^^

module assumptions {
    pure val NumberOfParties = 3

    pure val CorruptedBound  = 1

    pure val MaxRound        = 5

    pure val TapeCap         = 1
}

module utils {
    type Round_t = int

    pure def FirstRound : int = 0

    // ^^^^^

    type P_Sid_t = int

    type Sid_t = S_Sid | Z_Sid | P_Sid(P_Sid_t) | GClock_Sid

    pure def InvalidP_Sid : int = -1

    // ^^^^^

    type Flag_t = bool

    pure def One : Flag_t = true

    pure def Zero : Flag_t = false

    // ^^^^^

    type Option_t[a] = Some(a) | None

    // ^^^^^

    type Effects_t[a] = List[a]
}

// UC Framework
// ^^^^^^^^^^^^

module uc {
    import utils.*
    import assumptions.*

    type ITM[in, out, in_msg] = {
        sid                : Sid_t,
        input              : List[in],
        output             : List[out],
        incoming_messages  : List[in_msg],
    }

    type ItmEffect[in, out, in_msg] = ItmEffectUpdateInput(in)
                                    | ItmEffectUpdateOutput(out)
                                    | ItmEffectUpdateIncoming(in_msg)
                                    | ItmEffectPopInput
                                    | ItmEffectPopOutput
                                    | ItmEffectPopIncoming

    pure def ItmInit(sid: Sid_t) : ITM[in, out, incoming] = {
        sid               : sid,
        input             : [],
        output            : [],
        incoming_messages : [],
    }

    pure def PopTape(tape : List[a]) : List[a] = {
        if (length(tape) == 0) tape else tape.tail()
    }

    pure def ItmApplyEffect(itm : ITM[in, out, incoming], effect : ItmEffect[in, out, incoming]) : ITM[in, out, incoming] = {
        match (effect) {
            | ItmEffectUpdateInput(msg)    => itm.with("input", itm.input.append(msg))
            | ItmEffectUpdateOutput(msg)   => itm.with("output", itm.output.append(msg))
            | ItmEffectUpdateIncoming(msg) => itm.with("incoming_messages", itm.incoming_messages.append(msg))
            | ItmEffectPopInput            => itm.with("input", PopTape(itm.input))
            | ItmEffectPopOutput           => itm.with("output", PopTape(itm.output))
            | ItmEffectPopIncoming         => itm.with("incoming_messages", PopTape(itm.incoming_messages))
        }
    }

    pure def ReadNew(tape : List[a]) : Option_t[a] = {
        if (length(tape) == 0) None
        else Some(tape.head())
    }

    pure def ReadNewInput(itm) = {
        ReadNew(itm.input)
    }

    pure def ReadNewOutput(itm) = {
        ReadNew(itm.output)
    }

    pure def ReadNewIncoming(itm) = {
        ReadNew(itm.incoming_messages)
    }

    pure def ItmIsEmpty(itm : ITM[in, out, incoming]) : bool = {
        and {
            length(itm.input) == 0,
            length(itm.output) == 0,
            length(itm.incoming_messages) == 0,
        }
    }

    pure def ItmFits(itm : ITM[in, out, incoming]) : bool = {
        and {
            length(itm.input) <= TapeCap,
            length(itm.output) <= TapeCap,
            length(itm.incoming_messages) <= TapeCap,
        }
    }
}

// -----------------------------------------------------------------

// Ideal-world Model
// ^^^^^^^^^^^^^^^^

module iw {
    import uc.*
    import utils.*
    import assumptions.*

    // -----------------------------------------------------------------

    // Globals
    // ^^^^^^^

    var Z        : EnvironmentState
    var S        : SimulatorState
    var GClock   : ClockState
    var Parties  : PartiesState

    var prev_Z        : Option_t[EnvironmentState]
    var prev_S        : Option_t[SimulatorState]
    var prev_GClock   : Option_t[ClockState]
    var prev_Parties  : Option_t[PartiesState]

    // Set when a step needed more than TapeCap slots on some tape.
    var overflow : bool

    // -----------------------------------------------------------------

    // Effect
    // ^^^^^^^

    type IwEffect = GClockIwEffect(ClockEffect)
                  | EnvironmentIwEffect(EnvironmentEffect)
                  | SimulatorIwEffect(SimulatorEffect)
                  | PartiesIwEffect(PartiesEffect)

    type World = {
        z : EnvironmentState,
        s : SimulatorState,
        g : ClockState,
        p : PartiesState,
    }

    pure def IwApplyEffect(w : World, e : IwEffect) : World = {
        match e {
            | EnvironmentIwEffect(x) => w.with("z", EnvironmentApplyEffect(w.z, x))
            | SimulatorIwEffect(x)   => w.with("s", SimulatorApplyEffect(w.s, x))
            | GClockIwEffect(x)      => w.with("g", ClockApplyEffect(w.g, x))
            | PartiesIwEffect(x)     => w.with("p", PartiesApplyEffect(w.p, x))
        }
    }

    pure def WorldFits(w : World) : bool = {
        and {
            ItmFits(w.s.itm),
            ItmFits(w.g.itm),
            w.p.keys().forall(k => ItmFits(w.p.get(k).itm)),
        }
    }

    pure def Quiescent(s : SimulatorState, g : ClockState, p : PartiesState) : bool = {
        and {
            ItmIsEmpty(s.itm),
            ItmIsEmpty(g.itm),
            p.keys().forall(k => ItmIsEmpty(p.get(k).itm)),
        }
    }

    // -----------------------------------------------------------------

    // GClock
    // ^^^^^^

    type ClockInput = ClockInputReg(P_Sid_t)   // in the paper Psid.Reg()
                    | ClockInputRound(P_Sid_t) // in the paper Psid.Round()
                    | ClockInputOk(P_Sid_t)    // in the paper Psid.OK()

    type ClockOutput = ()

    type ClockIncoming = ClockIncomingRound             // in the paper Sim.Round() but adapted to the real world model
                       | ClockIncomingCorrupt (P_Sid_t) // modelling corruptions like Universally Composable Synchronous Computation instead

    type ClockITM = ITM[ClockInput, ClockOutput, ClockIncoming]

    type ClockState = {
        itm                : ClockITM,
        current_round      : Round_t,          // in the paper r
        registered_parties : Set[P_Sid_t],     // in the paper Reg
        corrupted_parties  : Set[P_Sid_t],     // in the paper C
        done               : P_Sid_t -> Flag_t // in the paper Done
    }

    type ClockAction = ClockActionRdInput | ClockActionRdIncoming

    type ClockEffect = ClockEffectUpdateItm(ItmEffect[ClockInput, ClockOutput, ClockIncoming])
                     | ClockEffectIncrementRound
                     | ClockEffectUpdateRegistered(P_Sid_t)
                     | ClockEffectUpdateCorrupted(P_Sid_t)
                     | ClockEffectUpdateDone({ p_sid : P_Sid_t, flag : Flag_t })

    pure def ClockApplyEffect(state : ClockState, effect : ClockEffect) : ClockState = {
        match (effect) {
            | ClockEffectUpdateItm(e)            => state.with("itm", ItmApplyEffect(state.itm, e))
            | ClockEffectUpdateRegistered(p_sid) => state.with("registered_parties", state.registered_parties.union(Set(p_sid)))
            | ClockEffectUpdateCorrupted(p_sid)  => state.with("corrupted_parties", state.corrupted_parties.union(Set(p_sid)))
            | ClockEffectUpdateDone(d)           => state.with("done", state.done.put(d.p_sid, d.flag))
            | ClockEffectIncrementRound          => state.with("current_round", if (state.current_round < MaxRound) state.current_round + 1 else MaxRound) // saturates at MaxRound so the state space is finite
        }
    }

    pure def ClockInit : ClockState = {
        itm                : ItmInit(GClock_Sid),
        current_round      : FirstRound,
        registered_parties : Set(),
        corrupted_parties  : Set(),
        done               : Map()
    }

    pure def ClockRegister(clock : ClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        val effects = [GClockIwEffect(ClockEffectUpdateRegistered(p_sid))]
        if (clock.registered_parties.contains(p_sid)) {
            effects
                .append(PartiesIwEffect(PartiesEffectUpdateItm({p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRegisterOk)})))
        }
        else {
            effects
                .append(GClockIwEffect(ClockEffectUpdateDone({ p_sid : p_sid, flag: Zero })))
                .append(PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRegisterOk) })))
        }
    }

    pure def ClockPartyRound(clock : ClockState, p_sid: P_Sid_t) : Effects_t[IwEffect] = {
        [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRound(clock.current_round)) }))]
    }

    pure def ClockSimulatorRound(clock : ClockState) : Effects_t[IwEffect] = {
        [SimulatorIwEffect(SimulatorEffectUpdateItm(ItmEffectUpdateIncoming(SimulatorIncomingRound(clock.current_round))))]
    }

    pure def ClockOk(clock : ClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        if (not(clock.registered_parties.contains(p_sid))) {
            [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputFailed) }))]
        } else {
            if (not((clock.registered_parties.exclude(clock.corrupted_parties))
                        .exists(sid => clock.done.put(p_sid, One).get(sid) == Zero)))
                clock.done.keys().exclude(clock.corrupted_parties).fold([], (acc, k) =>
                        acc.append(GClockIwEffect(ClockEffectUpdateDone({ p_sid : k, flag : Zero }))))
                    .append(GClockIwEffect(ClockEffectIncrementRound))
            else [ GClockIwEffect(ClockEffectUpdateDone({ p_sid : p_sid, flag : One }))
                 , SimulatorIwEffect(SimulatorEffectUpdateItm(ItmEffectUpdateIncoming(SimulatorIncomingOk(p_sid))))
                 , PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRoundOk) })) ]
        }
    }

    pure def ClockCorrupt(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateCorrupted(p_sid))]
    }

    pure def ClockTransition(which : ClockAction, clock : ClockState) : Effects_t[IwEffect] = {
        match which {
            | ClockActionRdInput    => {
                match ReadNewInput(clock.itm) {
                    | Some(input_message) => {
                        (match (input_message) {
                            | ClockInputReg(p_sid)   => ClockRegister(clock, p_sid)
                            | ClockInputRound(p_sid) => ClockPartyRound(clock, p_sid)
                            | ClockInputOk(p_sid)    => ClockOk(clock, p_sid)
                        }).append(GClockIwEffect(ClockEffectUpdateItm(ItmEffectPopInput)))
                    }
                    | None => []
                }
            }
            | ClockActionRdIncoming => {
                match ReadNewIncoming(clock.itm) {
                    | Some(incoming_message) => {
                        (match incoming_message {
                            | ClockIncomingRound          => ClockSimulatorRound(clock)
                            | ClockIncomingCorrupt(p_sid) => ClockCorrupt(p_sid)
                        }).append(GClockIwEffect(ClockEffectUpdateItm(ItmEffectPopIncoming)))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // Simulator
    // ^^^^^^^^^

    type SimulatorInput = ()

    type SimulatorOutput = ()

    type SimulatorIncoming = SimulatorIncomingRound(Round_t)
                           | SimulatorIncomingOk(P_Sid_t )


    type SimulatorITM = ITM[SimulatorInput, SimulatorOutput, SimulatorIncoming]

    type SimulatorState = {
        itm               : SimulatorITM,
        parties_that_oked : Set[P_Sid_t],
        corrupted_parties : Set[P_Sid_t],
        current_round     : Round_t
    }

    type SimulatorAction = SimulatorActionCorrupt(P_Sid_t) | SimulatorActionRoundRequest | SimulatorActionRdIncoming

    type SimulatorEffect = SimulatorEffectUpdateItm(ItmEffect[SimulatorInput, SimulatorOutput, SimulatorIncoming])
                         | SimulatorEffectUpdatedOked(P_Sid_t)
                         | SimulatorEffectUpdateCorrupted(P_Sid_t)
                         | SimulatorEffectUpdateRound(Round_t)

    pure def SimulatorApplyEffect(state : SimulatorState, effect : SimulatorEffect) : SimulatorState = {
        match effect {
            | SimulatorEffectUpdateItm(e)           => state.with("itm", ItmApplyEffect(state.itm, e))
            | SimulatorEffectUpdatedOked(p_sid)     => state.with("parties_that_oked", state.parties_that_oked.union(Set(p_sid)))
            | SimulatorEffectUpdateCorrupted(p_sid) => state.with("corrupted_parties", state.corrupted_parties.union(Set(p_sid)))
            | SimulatorEffectUpdateRound(round)     => state.with("current_round", round)
        }
    }

    pure def SimulatorInit : SimulatorState = {
        itm               : ItmInit(S_Sid),
        parties_that_oked : Set(),          
        corrupted_parties : Set(),
        current_round     : FirstRound
    }

    pure def SimulatorRound : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateIncoming(ClockIncomingRound)))]
    }

    pure def SimulatorRoundResponse(round : Round_t) : Effects_t[IwEffect] = {
        [SimulatorIwEffect(SimulatorEffectUpdateRound(round))]
    }

    pure def SimulatorCorrupt(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [ GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateIncoming(ClockIncomingCorrupt(p_sid))))
        , SimulatorIwEffect(SimulatorEffectUpdateCorrupted(p_sid)) ]
    }

    pure def SimulatorOked(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [SimulatorIwEffect(SimulatorEffectUpdatedOked(p_sid))]
    }

    pure def SimulatorNumberOfCorrupted(s : SimulatorState) : int = {
        size(s.corrupted_parties)
    }

    pure def SimulatorTransition(which : SimulatorAction, s : SimulatorState, quiet : bool) : Effects_t[IwEffect] = {
        match which {
            | SimulatorActionCorrupt(p_sid) => if (quiet) 
                                               if (size(s.corrupted_parties) < CorruptedBound) SimulatorCorrupt(p_sid) 
                                               else [] else []
            | SimulatorActionRoundRequest   => if (quiet) SimulatorRound else []
            | SimulatorActionRdIncoming     => match ReadNewIncoming(s.itm) {
                                                    | Some(incoming_message) => {
                                                        (match incoming_message {
                                                            | SimulatorIncomingRound(round) => SimulatorRoundResponse(round)
                                                            | SimulatorIncomingOk(p_sid)    => SimulatorOked(p_sid)
                                                        }).append(SimulatorIwEffect(SimulatorEffectUpdateItm(ItmEffectPopIncoming)))
                                                    }
                                                    | None => []
                                               }
        }
    }

    // -----------------------------------------------------------------

    // Environment
    // ^^^^^^^^^^^

    type EnvironmentOutput = EnvironmentOutputCorrupted(P_Sid_t)
                           | EnvironmentOutputRegisterOk(P_Sid_t)                         // in the paper ok
                           | EnvironmentOutputRoundOk(P_Sid_t)                            // in the paper ok
                           | EnvironmentOutputRound({ p_sid : P_Sid_t, round : Round_t }) // in the paper r
                           | EnvironmentOutputFailed(P_Sid_t)                             // in the paper ⊥

    type EnvironmentState = {
        registered : Set[P_Sid_t],        
        seen_round : P_Sid_t -> Round_t, 
    }

    type EnvironmentEffect = EnvironmentEffectObserve(EnvironmentOutput)
                           | EnvironmentEffectClearRounds

    type EnvironmentAction = EnvironmentActionSetOk(P_Sid_t)
                           | EnvironmentActionGetRound(P_Sid_t)
                           | EnvironmentActionRegister(P_Sid_t)

    pure def EnvironmentApplyEffect(state : EnvironmentState, effect : EnvironmentEffect) : EnvironmentState = {
        match (effect) {
            | EnvironmentEffectObserve(out) =>
                match out {
                    | EnvironmentOutputRegisterOk(p) => state.with("registered", state.registered.union(Set(p)))
                    | EnvironmentOutputRound(r)      => state.with("seen_round", state.seen_round.put(r.p_sid, r.round))
                    | _                              => state
                }
            | EnvironmentEffectClearRounds  => state.with("seen_round", Map())
        }
    }

    pure def EnvironmentInit : EnvironmentState = { registered : Set(), seen_round : Map() }

    pure def EnvironmentRound(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(PartiesInputRound) }))]
    }

    pure def EnvironmentOk(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [ PartiesIwEffect(PartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(PartiesInputOk) }))
        , EnvironmentIwEffect(EnvironmentEffectClearRounds) ]
    }

    pure def EnvironmentReg(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
         [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(PartiesInputReg) }))]
    }

    pure def EnvironmentAllRegistered(z : EnvironmentState) : bool = {
        size(z.registered) >= NumberOfParties
    }

    pure def EnvironmentTransition(which : EnvironmentAction, z : EnvironmentState, quiet : bool) : Effects_t[IwEffect] = {
        if (not(quiet)) []
        else match which {
            | EnvironmentActionRegister(p_sid) => if (z.registered.contains(p_sid)) [] else EnvironmentReg(p_sid)
            | EnvironmentActionSetOk(p_sid)    => if (EnvironmentAllRegistered(z)) EnvironmentOk(p_sid) else []
            | EnvironmentActionGetRound(p_sid) => if (EnvironmentAllRegistered(z)) EnvironmentRound(p_sid) else []
        }
    }

    // -----------------------------------------------------------------

    // Dummy Parties
    // ^^^^^^^^^^^^^

    type PartiesInput = PartiesInputReg   // in the paper Psid.Reg()
                      | PartiesInputRound // in the paper Psid.Round()
                      | PartiesInputOk    // in the paper Psid.OK()

    type PartiesOutput = PartiesOutputRound(Round_t) // in the paper Psid.Round()
                       | PartiesOutputRegisterOk      // in the paper ok
                       | PartiesOutputRoundOk         // in the paper ok
                       | PartiesOutputFailed          // in the paper ⊥

    type PartiesIncoming = ()

    type PartyITM = ITM[PartiesInput, PartiesOutput, PartiesIncoming]

    type PartyState = {
        itm : PartyITM,
    }

    type PartiesState = P_Sid_t -> PartyState

    pure def get_p_sid(p : PartyState) : P_Sid_t = {
        match (p.itm.sid) {
            | P_Sid(p_sid) => p_sid
            | _            => InvalidP_Sid
        }
    }

    type PartiesAction = PartiesActionRdInput | PartiesActionRdOutput

    type PartiesEffect = PartiesEffectUpdateItm({p_sid : P_Sid_t, effect : ItmEffect[PartiesInput, PartiesOutput, PartiesIncoming]})

    pure def PartiesApplyEffect(state : PartiesState, effect : PartiesEffect) : PartiesState = {
        match (effect) {
            | PartiesEffectUpdateItm(r) => state.put(r.p_sid, state.get(r.p_sid).with("itm", ItmApplyEffect(state.get(r.p_sid).itm, r.effect)))
        }
    }

    // Action called by Z.
    // It initializes P's state.
    pure def PartiesInit : PartiesState = 1.to(NumberOfParties).mapBy(i => ({ itm : ItmInit(P_Sid(i)) }))

    // Action called by the party when receiving Reg from Z on
    // the input-tape.
    // Finally it puts an Reg message in the G-Clock's input-tape.
    pure def PartiesRegister(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateInput(ClockInputReg(p_sid))))]
    }

    pure def PartiesRound(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateInput(ClockInputRound(p_sid))))]
    }

    pure def PartiesRoundToZ(p_sid : P_Sid_t, round : Round_t) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(EnvironmentEffectObserve(EnvironmentOutputRound({ p_sid : p_sid, round : round })))]
    }

    pure def PartiesOk(p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateInput(ClockInputOk(p_sid))))]
    }

    pure def PartiesMaybeOkToZ(p_sid : P_Sid_t, response : PartiesOutput) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(EnvironmentEffectObserve(match response {
                                                        | PartiesOutputRoundOk    => EnvironmentOutputRoundOk(p_sid)
                                                        | PartiesOutputRegisterOk => EnvironmentOutputRegisterOk(p_sid)
                                                        | PartiesOutputFailed     => EnvironmentOutputFailed(p_sid)
                                                        | _                       => EnvironmentOutputFailed(p_sid)}))]
    }

    pure def PartiesTransition(which : PartiesAction, p_sid : P_Sid_t, parties : PartiesState) : Effects_t[IwEffect] = {
        match which {
            | PartiesActionRdInput    => {
                match ReadNewInput(parties.get(p_sid).itm) {
                    | Some(input_message) => {
                        (match (input_message) {
                            | PartiesInputReg   => PartiesRegister(p_sid)
                            | PartiesInputRound => PartiesRound(p_sid)
                            | PartiesInputOk    => PartiesOk(p_sid)
                        }).append(PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectPopInput })))
                    }
                    | None => []
                }
            }
            | PartiesActionRdOutput => {
                match ReadNewOutput(parties.get(p_sid).itm) {
                    | Some(output_message) => {
                        (match output_message {
                            | PartiesOutputRound(r)   => PartiesRoundToZ(p_sid, r)
                            | PartiesOutputFailed     => PartiesMaybeOkToZ(p_sid, PartiesOutputFailed)
                            | PartiesOutputRegisterOk => PartiesMaybeOkToZ(p_sid, PartiesOutputRegisterOk)
                            | PartiesOutputRoundOk    => PartiesMaybeOkToZ(p_sid, PartiesOutputRoundOk)
                        }).append(PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectPopOutput })))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // Main
    // ^^^^

    action IwInit = all {
        Z'        = EnvironmentInit,
        S'        = SimulatorInit,
        GClock'   = ClockInit,
        Parties'  = PartiesInit,
        overflow' = false,

        // for time liveness property
        prev_Z'       = None,
        prev_S'       = None,
        prev_GClock'  = None,
        prev_Parties' = None
    }

    action IwStep = all {
        val quiet = Quiescent(S, GClock, Parties)
        nondet who = oneOf(Set(Z_Sid, S_Sid, GClock_Sid, P_Sid(InvalidP_Sid)))

        match who {
            | Z_Sid => {
                // Environment
                nondet p_sid_z = oneOf(1.to(NumberOfParties))
                nondet which_z = oneOf(Set( EnvironmentActionRegister(p_sid_z)
                                          , EnvironmentActionSetOk(p_sid_z)
                                          , EnvironmentActionGetRound(p_sid_z)))

                Update(EnvironmentTransition(which_z, Z, quiet))
            }

            | P_Sid(_) => {
                // Parties
                nondet which_p = oneOf(Set( PartiesActionRdOutput
                                          , PartiesActionRdInput ))
                nondet p_sid_p = oneOf(1.to(NumberOfParties))

                Update(PartiesTransition(which_p, p_sid_p, Parties))
            }

            | S_Sid => {
                // Simulator
                nondet p_sid_s = oneOf(1.to(NumberOfParties))
                nondet which_s = oneOf(Set( SimulatorActionCorrupt(p_sid_s)
                                          , SimulatorActionRoundRequest
                                          , SimulatorActionRdIncoming))

                Update(SimulatorTransition(which_s, S, quiet))
            }

            | GClock_Sid => {
                // GClock
                nondet which_g = oneOf(Set( ClockActionRdInput
                                          , ClockActionRdIncoming ))

                Update(ClockTransition(which_g, GClock))
            }
        },

        // for time liveness property
        prev_Z'       = Some(Z),
        prev_S'       = Some(S),
        prev_GClock'  = Some(GClock),
        prev_Parties' = Some(Parties)
    }

    action Update(effects : Effects_t[IwEffect]) : bool = {
        val w = effects.foldl({ z : Z, s : S, g : GClock, p : Parties }, (acc, e) => IwApplyEffect(acc, e))

        if (WorldFits(w)) all {
            Z'        = w.z,
            S'        = w.s,
            GClock'   = w.g,
            Parties'  = w.p,
            overflow' = overflow
        } else all {
            Z'        = Z,
            S'        = S,
            GClock'   = GClock,
            Parties'  = Parties,
            overflow' = true
        }
    }

    // -----------------------------------------------------------------

    // Properties
    // ^^^^^^^^^^

    // MUST FAIL
    // ^^^^^^^^^

    val RoundPastBound =
        GClock.current_round < MaxRound

    val SeenTwoRounds = 
        size(Z.seen_round.keys()) < 2

    // MUST PASS
    // ^^^^^^^^^

    // For correctness
    val NoOverflow    = 
        not(overflow)
        
    val RoundBounded  = 
        GClock.current_round <= MaxRound

    // Property 1: Time Agreement: If two parties query the time and no OK requests have been sent in the middle then G-clock responds with the same time.
    val TimeAgreement =
        Z.seen_round.keys().forall(p1 =>
            Z.seen_round.keys().forall(p2 =>
                Z.seen_round.get(p1) == Z.seen_round.get(p2)
            )
        )

    // Property 2: TimeLiveness: If all honest registered parties are ready, then time advances. 
    val TimeLiveness =
        match prev_GClock {
            | Some(pc) =>
                (pc.current_round < GClock.current_round).implies(
                    match ReadNewInput(pc.itm) {
                        | Some(i) =>
                            match i {
                                | ClockInputOk(p) => and {
                                    pc.registered_parties.contains(p),
                                    pc.registered_parties.exclude(pc.corrupted_parties)
                                        .forall(q => q == p or pc.done.get(q) == One),
                                }
                                | _ => false
                            }
                            
                        | _ => false
                    })
            | None => true
        }

    val AllProps = and {
        NoOverflow,
        RoundBounded,
        TimeAgreement
    }
}

// -----------------------------------------------------------------

// Real-world Model
// ^^^^^^^^^^^^^^^^

module rw {
    import utils.*
}

// Main
// ^^^^

module uc_gclock {
    import iw.*

    action init = all {
        IwInit
    }

    action step = all {
        IwStep
    }
}
