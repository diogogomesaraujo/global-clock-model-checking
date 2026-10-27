// Model Checking G-Clock
// from: https://eprint.iacr.org/2026/292.pdf

// -----------------------------------------------------------------

// Utils
// ^^^^^

module assumptions {
    pure val NumberOfParties = 2
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

    type Pointer_t = int // points to the element it will evaluate (not the one it has already evaluated) 

    pure def NotPointing : Pointer_t = 0

    // ^^^^^

    type Option_t[a] = Some(a) | None

    // ^^^^^

    type Effects_t[a] = List[a]
}

// UC Framework
// ^^^^^^^^^^^^

module uc {
    import utils.*

    type ITM[in, out, in_msg] = {
        sid                : Sid_t,
        input              : List[in],
        output             : List[out],
        incoming_messages  : List[in_msg],
        input_pointer      : Pointer_t,
        output_pointer     : Pointer_t,
        incoming_pointer   : Pointer_t,
    }

    type ItmEffect[in, out, in_msg] = ItmEffectUpdateInput(in)
                                    | ItmEffectUpdateOutput(out)
                                    | ItmEffectUpdateIncoming(in_msg)
                                    | ItmEffectIncrementInputPointer
                                    | ItmEffectIncrementOutputPointer
                                    | ItmEffectIncrementIncomingPointer

    pure def ItmInit(sid: Sid_t) : ITM[in, out, incoming] = {
        sid               : sid,
        input             : [],
        output            : [],
        incoming_messages : [],
        input_pointer     : NotPointing,
        output_pointer    : NotPointing,
        incoming_pointer  : NotPointing,
    }

    pure def ItmApplyEffect(itm : ITM[in, out, incoming], effect : ItmEffect) : ITM[in, out, incoming] = {
        match (effect) {
            | ItmEffectUpdateInput(msg)         => itm.with("input", itm.input.append(msg))
            | ItmEffectUpdateOutput(msg)        => itm.with("output", itm.output.append(msg))
            | ItmEffectUpdateIncoming(msg)      => itm.with("incoming_messages", itm.incoming_messages.append(msg))
            | ItmEffectIncrementInputPointer    => itm.with("input_pointer", itm.input_pointer + 1)
            | ItmEffectIncrementOutputPointer   => itm.with("output_pointer", itm.output_pointer + 1)
            | ItmEffectIncrementIncomingPointer => itm.with("incoming_pointer", itm.incoming_pointer + 1)
        }
    }

    pure def ItmApplyEffects(state : ITM[in, out, incoming], effects : Effects_t[ItmEffect]) : ITM[in, out, incoming] = {
        effects.foldl(state, (acc, e) => ItmApplyEffect(acc, e))
    }

    pure def ReadNew(tape, pointer) = {
        if (length(tape)      == 0) None
        else if (length(tape) <= pointer) None
        else Some(tape[pointer])
    }

    pure def ReadNewInput(itm) = {
        ReadNew(itm.input, itm.input_pointer)
    }

    pure def ReadNewOutput(itm) = {
        ReadNew(itm.output, itm.output_pointer)
    }

    pure def ReadNewIncoming(itm) = {
        ReadNew(itm.incoming_messages, itm.incoming_pointer)
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

    var Z       : EnvironmentState
    var S       : SimulatorState
    var GClock  : ClockState
    var Parties : PartiesState

    // -----------------------------------------------------------------

    // Effect
    // ^^^^^^^

    type IwEffect = GClockIwEffect(ClockEffect)
                  | EnvironmentIwEffect(EnvironmentEffect)
                  | SimulatorIwEffect(SimulatorEffect)
                  | PartiesIwEffect(PartiesEffect)

    // -----------------------------------------------------------------

    // GClock
    // ^^^^^^

    type ClockInput = ClockInputReg(P_Sid_t)   // in the paper Psid.Reg()
                    | ClockInputRound(P_Sid_t) // in the paper Psid.Round()
                    | ClockInputOk(P_Sid_t)    // in the paper Psid.OK()

    type ClockOutput = ()

    type ClockIncoming = ClockIncomingRound                         // in the paper Sim.Round() but adapted to the real world model
                       | ClockIncomingCorrupt (P_Sid_t) // note: modelling corruptions like Universally Composable Synchronous Computation instead

    type ClockITM = ITM[ClockInput, ClockOutput, ClockIncoming]

    type ClockState = {
        itm                : ClockITM,
        current_round      : Round_t,        // in the paper r
        registered_parties : Set[P_Sid_t],   // in the paper Reg
        corrupted_parties  : Set[P_Sid_t],   // in the paper C
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
            | ClockEffectIncrementRound          => state.with("current_round", state.current_round + 1)
        }
    }

    pure def ClockApplyEffects(state : ClockState, effects : Effects_t[ClockEffect]) : ClockState = {
        effects.foldl(state, (acc, e) => ClockApplyEffect(acc, e))
    }

    // Action called by Z.
    // It initializes the G-Clock's state.
    pure def ClockInit : ClockState = {
        itm                : ItmInit(GClock_Sid),
        current_round      : FirstRound,
        registered_parties : Set(),
        corrupted_parties  : Set(),
        done               : Map()
    }

    // Action called by the clock when receiving a Reg request from P on the 
    // input tape.
    // It registers the party with sid P_Sid and, if it was not previously
    // registered it sets done[P_Sid] to 0.
    // Finally it puts an Ok message in P's output-tape.
    pure def ClockRegister(GClock : ClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        val effects = [GClockIwEffect(ClockEffectUpdateRegistered(p_sid))]
        if (GClock.registered_parties.contains(p_sid)) {
            effects
                .append(PartiesIwEffect(PartiesEffectUpdateItm({p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRegisterOk)})))
        }
        else {
            effects
                .append(GClockIwEffect(ClockEffectUpdateDone({ p_sid : p_sid, flag: Zero })))
                .append(PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRegisterOk) })))
        }
    }

    // Action called by the clock when receiving a PartyRoundRequest request 
    // from P on the input tape.
    // Finally it puts a RoundResponse message in P's output-tape.
    pure def ClockPartyRound(GClock : ClockState, p_sid: P_Sid_t) : Effects_t[IwEffect] = {
        [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRound(GClock.current_round)) }))]
    }

    // Action called by the clock when receiving a Sim.Round() request 
    // from S on the incoming messages tape.
    // Finally it puts a RoundResponse message in S's incoming messages tape.
    pure def ClockSimulatorRound(GClock : ClockState) : Effects_t[IwEffect] = {
        [SimulatorIwEffect(SimulatorEffectUpdateItm(ItmEffectUpdateIncoming(SimulatorIncomingRound(GClock.current_round))))]
    }

    pure def ClockOk(GClock : ClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        if (not(GClock.registered_parties.contains(p_sid))) {
            [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputFailed) }))]
        } else { 
            if (not((GClock.registered_parties.exclude(GClock.corrupted_parties))
                        .exists(sid => GClock.done.put(p_sid, One).get(sid) == Zero))) // because P stil has his flag set to O
                GClock.done.keys().exclude(GClock.corrupted_parties).fold([], (acc, k) => 
                        acc.append(GClockIwEffect(ClockEffectUpdateDone({ p_sid : k, flag : Zero }))))
                    .append(GClockIwEffect(ClockEffectIncrementRound))
            else [ GClockIwEffect(ClockEffectUpdateDone({ p_sid : p_sid, flag : One }))
                 , SimulatorIwEffect(SimulatorEffectUpdateItm(ItmEffectUpdateIncoming(SimulatorIncomingOk(p_sid))))
                 , PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectUpdateOutput(PartiesOutputRoundOk) })) ]
        }
    }

    pure def ClockCorrupt(GClock: ClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateCorrupted(p_sid))]
    }

    pure def ClockTransition(which : ClockAction, GClock : ClockState, Z : EnvironmentState, S : SimulatorState, Parties : PartiesState) : Effects_t[IwEffect] = {
        match which {
            | ClockActionRdInput    => {
                match ReadNewInput(GClock.itm) {
                    | Some(input_message) => {
                        (match (input_message) {
                            | ClockInputReg(p_sid)   => ClockRegister(GClock, p_sid)
                            | ClockInputRound(p_sid) => ClockPartyRound(GClock, p_sid)
                            | ClockInputOk(p_sid)    => ClockOk(GClock, p_sid)
                            | _ => []
                        }).append(GClockIwEffect(ClockEffectUpdateItm(ItmEffectIncrementInputPointer)))
                    }
                    | None => []
                }
            }
            | ClockActionRdIncoming => { 
                match ReadNewIncoming(GClock.itm) {
                    | Some(incoming_message) => {
                        (match incoming_message {
                            | ClockIncomingRound      => ClockSimulatorRound(GClock)
                            | ClockIncomingCorrupt(p_sid) => ClockCorrupt(GClock, p_sid)
                        }).append(GClockIwEffect(ClockEffectUpdateItm(ItmEffectIncrementIncomingPointer)))
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

    pure def SimulatorApplyEffects(state : SimulatorState, effects : Effects_t[SimulatorEffect]) : SimulatorState = {
        effects.foldl(state, (acc, e) => SimulatorApplyEffect(acc, e))
    }

    // Action called by Z.
    // It initializes S's state.
    pure def SimulatorInit : SimulatorState = {
        itm               : ItmInit(S_Sid), // for now here because we don't need to consider the machine before activation
        parties_that_oked : Set(),             // oked the current round
        corrupted_parties : Set(),
        current_round     : FirstRound
    }

    pure def SimulatorRound() : Effects_t[IwEffect] = {
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

    pure def SimulatorTransition(which : SimulatorAction, S : SimulatorState) : Effects_t[IwEffect] = {
        match which {
            | SimulatorActionCorrupt(p_sid) => SimulatorCorrupt(p_sid)
            | SimulatorActionRoundRequest   => SimulatorRound
            | SimulatorActionRdIncoming     => match ReadNewIncoming(S.itm) {
                                                    | Some(incoming_message) => {
                                                        (match incoming_message {
                                                            | SimulatorIncomingRound(round) => SimulatorRoundResponse(round)
                                                            | SimulatorIncomingOk(p_sid)    => SimulatorOked(p_sid)
                                                        }).append(SimulatorIwEffect(SimulatorEffectUpdateItm(ItmEffectIncrementIncomingPointer)))
                                                    }
                                                    | None => []
                                               }
        }
    }

    // -----------------------------------------------------------------

    // Environment
    // ^^^^^^^^^^^

    type EnvironmentInput = ()

    type EnvironmentOutput = EnvironmentOutputCorrupted(P_Sid_t)
                           | EnvironmentOutputRegisterOk(P_Sid_t)                         // in the paper ok
                           | EnvironmentOutputRoundOk(P_Sid_t)                            // in the paper ok
                           | EnvironmentOutputRound({ p_sid : P_Sid_t, round : Round_t }) // in the paper r
                           | EnvironmentOutputFailed(P_Sid_t)                             // in the paper ⊥

    type EnvironmentIncoming = ()

    type EnvironmentITM = ITM[EnvironmentInput, EnvironmentOutput, EnvironmentIncoming]

    type EnvironmentState = {
        itm : EnvironmentITM,
    }

    type EnvironmentEffect = | EnvironmentEffectUpdateItm(ItmEffect[EnvironmentInput, EnvironmentOutput, EnvironmentIncoming])

    type EnvironmentAction = EnvironmentActionSetOk(P_Sid_t) 
                           | EnvironmentActionGetRound(P_Sid_t) 
                           | EnvironmentActionRegister(P_Sid_t)

    pure def EnvironmentApplyEffect(state : EnvironmentState, effect : EnvironmentEffect) : EnvironmentState = {
        match (effect) {
            | EnvironmentEffectUpdateItm(e) => state.with("itm", ItmApplyEffect(state.itm, e))
        }
    }

    pure def EnvironmentApplyEffects(state : EnvironmentState, effects : Effects_t[EnvironmentEffect]) : EnvironmentState = {
        effects.foldl(state, (acc, e) => EnvironmentApplyEffect(acc, e))
    }

    // Action called by the model checker.
    // It initializes Z's state.
    pure def EnvironmentInit : EnvironmentState = { itm : ItmInit(Z_Sid) }

    pure def EnvironmentRound(p_sid : P_Sid_t, Parties : PartiesState) : Effects_t[IwEffect] = {
        [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(PartiesInputRound) }))]
    }

    pure def EnvironmentOk(p_sid : P_Sid_t, Parties : PartiesState) : Effects_t[IwEffect] = {
        [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(PartiesInputOk) }))]
    }

    pure def EnvironmentReg(p_sid : P_Sid_t, Parties : PartiesState) : Effects_t[IwEffect] = {
         [PartiesIwEffect(PartiesEffectUpdateItm({ p_sid: p_sid, effect : ItmEffectUpdateInput(PartiesInputReg) }))]
    }

    pure def EnvironmentAllRegistered(Z : EnvironmentState) : bool = {
        length(Z.itm.output.select(out => match out {
            | EnvironmentOutputRegisterOk(_) => true
            | _             => false
        })) >= NumberOfParties
    }

    pure def EnvironmentNotRegistered(Z : EnvironmentState) : Set[P_Sid_t] = {
    val registered = Z.itm.output.foldl(Set(), (acc, out) =>
            match out {
                | EnvironmentOutputRegisterOk(p) => acc.union(Set(p))
                | _ => acc
            })
        1.to(NumberOfParties).exclude(registered)
    }

    pure def EnvironmentTransition(which : EnvironmentAction, Parties : PartiesState) : Effects_t[IwEffect] = {
        match which {
            | EnvironmentActionSetOk(p_sid)    => EnvironmentOk(p_sid, Parties)
            | EnvironmentActionGetRound(p_sid) => EnvironmentRound(p_sid, Parties)
            | EnvironmentActionRegister(p_sid) => EnvironmentReg(p_sid, Parties)
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
        current_round : Round_t,
        itm           : PartyITM,
    }

    type PartiesState = P_Sid_t -> PartyState

    pure def get_p_sid(P : PartyState) : P_Sid_t = {
        match (P.itm.sid) {
            | P_Sid(p_sid) => p_sid
            | _            => InvalidP_Sid
        }
    }

    type PartiesAction = PartiesActionRdInput | PartiesActionRdOutput 

    type PartiesEffect = PartiesEffectUpdateItm({p_sid : P_Sid_t, effect : ItmEffect[PartiesInput, PartiesOutput, PartiesIncoming]})
                       | PartiesEffectUpdateRound(P_Sid_t)

    pure def PartiesApplyEffect(state : PartiesState, effect : PartiesEffect) : PartiesState = {
        match (effect) {
            | PartiesEffectUpdateItm(r)   => state.put(r.p_sid, state.get(r.p_sid).with("itm", ItmApplyEffect(state.get(r.p_sid).itm, r.effect)))
            | PartiesEffectUpdateRound(p_sid) => state.put(p_sid, state.get(p_sid).with("current_round", state.get(p_sid).current_round + 1))
        }
    }

    pure def PartiesApplyEffects(state : PartiesState, effects : Effects_t[PartiesEffect]) : PartiesState = {
        effects.foldl(state, (acc, e) => PartiesApplyEffect(acc, e))
    }

    // Action called by Z.
    // It initializes P's state.
    pure def PartiesInit : PartiesState = 1.to(NumberOfParties).mapBy(i => ({ itm : ItmInit(P_Sid(i)), current_round : 0 }))

    // Action called by the party when receiving Reg from Z on
    // the input-tape.
    // Finally it puts an Reg message in the G-Clock's output-tape.
    pure def PartiesRegister(p_sid : P_Sid_t, GClock : ClockState, Z : EnvironmentState) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateInput(ClockInputReg(p_sid ))))]
    }

    pure def PartiesRegisterToZ(p_sid : P_Sid_t, Z : EnvironmentState, response : EnvironmentOutput) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(EnvironmentEffectUpdateItm(ItmEffectUpdateOutput(response)))]
    }

    pure def PartiesRound(p_sid : P_Sid_t, GClock : ClockState) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateInput(ClockInputRound(p_sid))))]
    }

    pure def PartiesRoundToZ(p_sid : P_Sid_t, Z : EnvironmentState, round : Round_t) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(EnvironmentEffectUpdateItm(ItmEffectUpdateOutput(EnvironmentOutputRound({ p_sid : p_sid, round : round }))))]
    }

    pure def PartiesOk(GClock : ClockState, p_sid : P_Sid_t) : Effects_t[IwEffect] = {
        [GClockIwEffect(ClockEffectUpdateItm(ItmEffectUpdateInput(ClockInputOk(p_sid))))]
    }

    pure def PartiesMaybeOkToZ(p_sid : P_Sid_t, Z : EnvironmentState, response : PartiesOutput) : Effects_t[IwEffect] = {
        [EnvironmentIwEffect(EnvironmentEffectUpdateItm(ItmEffectUpdateOutput(match response {
                                                        | PartiesOutputRoundOk    => EnvironmentOutputRoundOk(p_sid)
                                                        | PartiesOutputRegisterOk => EnvironmentOutputRegisterOk(p_sid)
                                                        | PartiesOutputFailed     => EnvironmentOutputFailed(p_sid)
                                                        | _                       => EnvironmentOutputFailed(p_sid)})))]
    }

    pure def PartiesTransition(which : PartiesAction, p_sid : P_Sid_t, Parties : PartiesState, GClock : ClockState, Z : EnvironmentState) : Effects_t[IwEffect] = {
        match which {
            | PartiesActionRdInput    => {
                match ReadNewInput(Parties.get(p_sid).itm) {
                    | Some(input_message) => {
                        (match (input_message) {
                            | PartiesInputReg   => PartiesRegister(p_sid, GClock, Z)
                            | PartiesInputRound => PartiesRound(p_sid, GClock)
                            | PartiesInputOk    => PartiesOk(GClock, p_sid)
                            | _ => []
                        }).append(PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectIncrementInputPointer })))
                    }
                    | None => []
                }
            }
            | PartiesActionRdOutput => { 
                match ReadNewOutput(Parties.get(p_sid).itm) {
                    | Some(output_message) => {
                        (match output_message {
                            | PartiesOutputRound(r)   => PartiesRoundToZ(p_sid, Z, r)
                            | PartiesOutputFailed     => PartiesMaybeOkToZ(p_sid, Z, PartiesOutputFailed)
                            | PartiesOutputRegisterOk => PartiesMaybeOkToZ(p_sid, Z, PartiesOutputRegisterOk)
                            | PartiesOutputRoundOk    => PartiesMaybeOkToZ(p_sid, Z, PartiesOutputRoundOk)
                        }).append(PartiesIwEffect(PartiesEffectUpdateItm({ p_sid : p_sid, effect : ItmEffectIncrementOutputPointer })))
                    }
                    | None => []
                }
            }
        }
    }

    // -----------------------------------------------------------------

    // Main
    // ^^^^

    // all parties begin already activated by the environment. 
    // in the ideal world he assume all parties are registered before
    // they start interacting with the GClock. 
    action IwInit = all {
        Z'       = EnvironmentInit,
        S'       = SimulatorInit,
        GClock'  = ClockInit,
        Parties' = PartiesInit
    }

    action IwStep = {
       if (EnvironmentAllRegistered(Z)) {
            // Environment
            nondet p_sid_z = oneOf(1.to(NumberOfParties))
            nondet which_z = oneOf(Set( EnvironmentActionRegister(p_sid_z)
                                      , EnvironmentActionSetOk(p_sid_z)
                                      , EnvironmentActionGetRound(p_sid_z)))

            // Parties
            nondet which_p = oneOf(Set( PartiesActionRdOutput
                                      , PartiesActionRdInput ))

            // Simulator
            nondet p_sid_s = oneOf(1.to(NumberOfParties))
            nondet which_s = oneOf(Set( SimulatorActionCorrupt(p_sid_s)
                                      , SimulatorActionRoundRequest
                                      , SimulatorActionRdIncoming))

            // GClock
            nondet which_g = oneOf(Set( ClockActionRdInput
                                      , ClockActionRdIncoming ))

            val effects = 
                //Environment
                (
                    EnvironmentTransition(which_z, Parties)
                )
            
                // Parties
                .concat(
                    1.to(NumberOfParties).fold([], (acc, p_sid) => {
                        acc.concat(PartiesTransition(which_p, p_sid, Parties, GClock, Z))
                    })
                )

                // Simulator
                .concat(
                    SimulatorTransition(which_s, S)
                )

                // GClock
                .concat(
                    ClockTransition(which_g, GClock, Z, S, Parties)
                )

            Update(effects)
        } else {
            nondet p_sid = oneOf(EnvironmentNotRegistered(Z))

            val effects = 
                // Environment
                EnvironmentTransition(EnvironmentActionRegister(p_sid), Parties)

            Update(effects)
        }
    }

    action Update(effects) = all {
        Z' = EnvironmentApplyEffects(Z, effects.select(e => 
                match e {
                    | EnvironmentIwEffect(_) => true
                    | _          => false
                }
            ).foldl([], (acc, e) => match e {
                | EnvironmentIwEffect(e) => acc.append(e)
                | _          => acc
            })),
       S' = SimulatorApplyEffects(S, effects.select(e => 
                match e {
                    | SimulatorIwEffect(_) => true
                    | _          => false
                }
            ).foldl([], (acc, e) => match e {
                | SimulatorIwEffect(e) => acc.append(e)
                | _          => acc
            })),
        GClock' = ClockApplyEffects(GClock, effects.select(e => 
                match e {
                    | GClockIwEffect(_) => true
                    | _             => false
                }
            ).foldl([], (acc, e) => match e {
                | GClockIwEffect(e) => acc.append(e)
                | _          => acc
            })),
        Parties' = PartiesApplyEffects(Parties, effects.select(e => 
                match e {
                    | PartiesIwEffect(_) => true
                    | _          => false
                }
            ).foldl([], (acc, e) => match e {
                | PartiesIwEffect(e) => acc.append(e)
                | _          => acc
            }))
    }

    // -----------------------------------------------------------------

    // Properties
    // ^^^^^^^^^^


    // Time Agreement: If two parties query the time and no OK requests have been sent in the middle then G-clock responds with the same time.
    val TimeAgreement = 
        Parties.keys().forall(p1 => 
            Parties.keys().forall(p2 => 
                if (p1 != p2) {
                    match ReadNewOutput(Parties.get(p1).itm) {
                        | Some(res) => 
                            match res {
                                | PartiesOutputRound(r1) => 
                                    match ReadNewOutput(Parties.get(p2).itm) {
                                        | Some(res) => 
                                            match res {
                                                | PartiesOutputRound(r2) => 
                                                    r1 == r2
                                                | _ => true
                                            }
                                        | _ => true
                                    }
                                | _ => true
                            }
                        | _  => true
                    }
                } else true
            )
        )
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
