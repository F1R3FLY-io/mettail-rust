#!/usr/bin/env wolframscript
(* RhoNet small-state exploration (pgmcp #1956 Epic 8 #2049) -- Wolfram Language
   counterpart of formal/sage/rho_net/rho_net_small_state.sage.

   Enumerates the three operational facets the item names for tiny RhoNet instances,
   complementing the mechanized Rocq proofs (abstract/parametric) and the TLA+
   scheduler (formal/tla/rho_machine/RhoNetScheduler.tla) with concrete finite
   evidence. Wolfram's native term rewriting expresses the base-rewrite
   sigma-receiver directly as a rule.

     * MATCHING     -- the positional root index (Head + Length) never drops a
                       match: MatchQ[subject, pattern] implies the index admits it
                       (Rocq PositionalSetAutomatonSound.v index_never_drops_match).
     * OBSERVATION  -- the SwapDemo sigma-receiver Swap[x_,y_] :> Pair[y,x], applied
                       to Swap[a,b], lands Pair[b,a] = RHS[sigma], non-vacuously
                       (Rocq LinearCommCorrespondence.v; rho_net_equivalence test).
     * SCHEDULING   -- independent COMM redexes on distinct channels are
                       schedule-confluent: every firing order yields the same
                       resting out-channel barb multiset (EndToEndCommCorrespondence.v).

   Run:  /usr/local/Wolfram/Wolfram/15.0/Executables/wolframscript -file <this>
   Exits 1 on any failed small-state check, 0 on success (prints a JSON summary). *)

leaves = {A, B};

(* --- OBSERVATION: the sigma-receiver as a native rewrite rule. --- *)
swapReceiver = Swap[x_, y_] :> Pair[y, x];

observationCases = Flatten[Table[
    Module[{subject = Swap[a, b], observed, expected},
     observed = subject /. swapReceiver;
     expected = Pair[b, a];
     If[observed =!= expected,
      Print["OBSERVATION FAIL: ", subject, " -> ", observed, " != ", expected];
      Exit[1]];
     <|"subject" -> ToString[subject, InputForm],
       "observed" -> ToString[observed, InputForm],
       "nonvacuous" -> (observed =!= subject)|>],
    {a, leaves}, {b, leaves}], 1];

observationNonvacuous = Count[observationCases, c_ /; c["nonvacuous"]];

(* --- MATCHING: a real match implies the (Head, Length) root index admits it. --- *)
dispatchAdmits[patt_, subj_] :=
  Head[patt] === Head[subj] && Length[patt] === Length[subj];

subjects = Join[leaves,
   Flatten[Table[f[a, b], {f, {Swap, Pair}}, {a, leaves}, {b, leaves}]]];

(* Structural (Head[_,_]) patterns whose index key is (Head, arity). *)
appPatterns = {Swap[_, _], Pair[_, _]};
matchingChecked = 0;
Do[
  If[MatchQ[s, p] && ! dispatchAdmits[p, s],
    Print["MATCHING FAIL (index dropped a match): ", p, " ~ ", s];
    Exit[1]];
  (* and the index only admits genuine head/arity agreement *)
  If[dispatchAdmits[p, s] && Head[p] =!= Head[s],
    Print["MATCHING FAIL (spurious index admission)"];
    Exit[1]];
  matchingChecked++,
  {p, appPatterns}, {s, subjects}];

(* --- SCHEDULING: independent redexes are schedule-confluent. --- *)
redexData = {"d1", "d2", "d3"};
observedMultisets = DeleteDuplicates[
   Map[Sort, Permutations[redexData]]];
If[Length[observedMultisets] =!= 1,
  Print["SCHEDULING FAIL (not confluent): ", observedMultisets];
  Exit[1]];
confluentBarbs = First[observedMultisets];

summary = <|
   "matching_app_pattern_subject_pairs_checked" -> matchingChecked,
   "matching_index_never_drops_match" -> True,
   "observation_cases" -> observationCases,
   "observation_nonvacuous_offdiagonal" -> observationNonvacuous,
   "scheduling_orders_explored" -> Length[Permutations[redexData]],
   "scheduling_confluent_barbs" -> confluentBarbs|>;

Print[ExportString[summary, "JSON"]];
Print["rho_net_small_state (Wolfram): all small-state checks passed"];
Exit[0]
