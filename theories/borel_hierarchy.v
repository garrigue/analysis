From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop interval_inference.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import real_interval numfun esum measure lebesgue_measure.

(**md**************************************************************************)
(* # Basic facts about G-delta and F-sigma sets                               *)
(*                                                                            *)
(* ```                                                                        *)
(*         Gdelta S == S is countable intersection of open sets               *)
(*   Gdelta_dense S == S is a countable intersection of dense open sets       *)
(*         Fsigma S == S is countable union of closed sets                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import numFieldNormedType.Exports.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Gdelta_Fsigma.
Context {T : topologicalType}.
Implicit Type S : set T.

Definition Gdelta S :=
  exists2 F : (set T)^nat, (forall i, open (F i)) & S = \bigcap_i (F i).

Lemma open_Gdelta S : open S -> Gdelta S.
Proof. by exists (fun=> S)=> //; rewrite bigcap_const. Qed.

Definition Gdelta_dense S :=
  exists2 F : (set T)^nat,
    (forall i, open (F i) /\ dense (F i)) & S = \bigcap_i (F i).

Definition Fsigma S :=
  exists2 F : (set T)^nat, (forall i, closed (F i)) & S = \bigcup_i (F i).

Lemma closed_Fsigma S : closed S -> Fsigma S.
Proof. by exists (fun=> S)=> //; rewrite bigcup_const. Qed.

End Gdelta_Fsigma.

Lemma Gdelta_measurable {R : realType} (S : set R) : Gdelta S -> measurable S.
Proof.
move=> [] B oB ->; apply: bigcapT_measurable => i.
exact: open_measurable.
Qed.

Lemma Gdelta_subspace_open {R : realType} (A : set R) (S : set (subspace A)) :
  open A -> Gdelta S -> Gdelta (A `&` S).
Proof.
move=> oA [/= S_ oS_ US]; exists (fun n => A `&` (S_ n)).
  by move=> ?; rewrite open_setSI.
by rewrite bigcapIr// US.
Qed.

Section irrational_Gdelta.
Context {R : realType}.

Lemma irrational_Gdelta : Gdelta_dense (@irrational R).
Proof.
rewrite irrationalE.
have /pcard_eqP/bijPex[f bijf] := card_rat.
pose f1 := 'pinv_(fun => 0%R) [set: rat] f.
exists (fun n => ~` [set ratr (f1 n)]).
  move=> n; rewrite openC; split; last exact: dense_set1C.
  exact/accessible_closed_set1/hausdorff_accessible/Rhausdorff.
apply/seteqP; split => [/= r/= rE n _/= rf1n|/=r rE q _/= [_ -> qr]].
  by apply: (rE (f1 n)) => //=; exists (f1 n).
apply: (rE (f q)) => //=.
by rewrite /f1 pinvKV ?inE//=; exact: set_bij_inj bijf.
Qed.

End irrational_Gdelta.

Lemma not_rational_Gdelta (R : realType) : ~ Gdelta (@rational R).
Proof.
apply/forall2NP => A; apply/not_andP => -[oA ratrA].
have dense_A n : dense (A n).
  move=> D D0 /(@dense_rat R D D0); apply/subset_nonempty; apply: setIS.
  by rewrite -/(@rational R) ratrA; exact: bigcap_inf.
have [/= B oB irratB] := @irrational_Gdelta R.
pose C : (set R)^nat := fun n => A n `&` B n.
have C0 : set0 = \bigcap_i C i by rewrite bigcapI -ratrA -irratB setICr.
have /Baire : forall n, open (C n) /\ dense (C n).
  move=> n; split.
  - by apply: openI => //; apply oB.
  - by apply: denseI => //; apply oB.
by rewrite -C0; exact: dense0.
Qed.

Section perfectlynormalspace.
Context (R : realType) (T : topologicalType).

Definition normal_space_closed :=
  forall E F : set T, closed E -> closed F -> [disjoint E & F] ->
    exists E' F' : set T,
      [/\ open E', open F', [disjoint E' & F'], E `<=` E' & F `<=` F'].

Lemma normal_space_closedP : normal_space T <-> normal_space_closed.
Proof.
split.
  move=> nsT E G cE cG EG.
  have := nsT E cE (~` G).
  have /[swap]/[apply] [[G']] : set_nbhs E (~` G).
    apply/set_nbhsP; exists (~` G); split => //.
    - by rewrite openC.
    - exact/disj_setPLR.
  case/set_nbhsP => E' [oE' EE' E'G'] G'G.
  exists E'; exists (~` closure G'); split => //.
  - rewrite openC; exact: closed_closure.
  - exact/disj_setPRL/subsetC/(subset_trans E'G')/subset_closure.
  - exact/subsetCr.
move=> nscT E cE G /set_nbhsP[F] [/interior_id oF EF FG].
have [] := nscT E (closure (~` F)) cE.
- exact: closed_closure.
- apply/disj_setPLR/(subset_trans EF).
  by rewrite closure_setC setCK oF.
move=> E' [F'] [oE' /interior_id oF' HF' EH].
rewrite closure_setC => /subsetCl.
rewrite oF => F'F.
exists (~` F'); last by apply: subset_trans FG; rewrite closure_setC oF'.
apply/set_nbhsP; exists E'; split => //; exact/subsetCr/disj_setPRL.
Qed.

Definition perfectly_normal_space (x : R) :=
  forall E : set T, closed E -> 
    exists f : T -> R, continuous f /\ E = f @^-1` [set x].

Lemma perfectly_normal_spaceP x y : perfectly_normal_space x -> perfectly_normal_space y.
Proof.
move=>px E cE.
case:(px E cE) => f [] cf ->.
pose f' := f + cst (y - x). 
exists f'.
split.
  rewrite /f'.
  move=> z.
  apply: continuousD.
    exact:cf.
  exact:cst_continuous.
apply/seteqP.
rewrite /f' /cst /=.
split => z /=.
  rewrite addrfctE => ->.
  by rewrite subrKC.
rewrite addrfctE.
move/eqP.
by rewrite eq_sym -subr_eq opprB subrKC eq_sym => /eqP.
Qed.

Definition perfectly_normal_space' (x : R) :=
  forall E : set T, open E -> 
    exists f : T -> R, continuous f /\ E = f @^-1` ~`[set x].

Definition perfectly_normal_space01 :=
  forall E F : set T, closed E -> closed F -> [disjoint E & F] ->
    exists f : T -> R,
      [/\ continuous f, E = f @^-1` [set 0], F = f @^-1` [set 1]
        & range f `<=` `[0, 1]%classic].

Definition perfectly_normal_space_Gdelta :=
  normal_space T /\ forall E : set T, closed E -> Gdelta E.

Let perfectly_normal_space_12 :
  perfectly_normal_space_Gdelta -> perfectly_normal_space' 0.
Proof.
Admitted.

Let perfectly_normal_space_23 :
  perfectly_normal_space' 0 -> perfectly_normal_space 0.
Proof.
move=> pns' E cE.
case: (pns' (~`E)).
  by rewrite openC.
move=> f [cf f0].
exists f.
split=> //.
by rewrite -[RHS]setCK preimage_setC -f0 setCK.
Qed.

Lemma norm_preimage0 (f : T -> R) :
  continuous f ->
  exists f' : T -> R, [/\ continuous f', (forall x, f' x >= 0)
                        & f' @^-1` [set 0] = f @^-1` [set 0]].
Proof.
move=> cf; exists (fun x => `|f x|); split => //.
- move=> x; exact/continuous_comp/norm_continuous/cf.
- apply/seteqP; split => [x|x /= ->]; [exact: normr0_eq0 | by rewrite normr0].
Qed.

Let perfectly_normal_space_34 :
  perfectly_normal_space 0 -> perfectly_normal_space01.
Proof.
move=> pns0 E F cE cF EF.
have [_ [/norm_preimage0 [f [cf f_ge0 <-]] E0]] := pns0 E cE.
have [_ [/norm_preimage0 [g [cg g_ge0 <-]] F0]] := pns0 F cF.
have fg_gt0 x : f x + g x > 0.
  move: (f_ge0 x) (g_ge0 x).
  rewrite !le_eqVlt => /orP[/eqP|] Hf /orP[/eqP|] Hg; last exact: addr_gt0.
  + by move: EF; rewrite E0 F0 => /disj_setPRL/(_ x); elim.
  + by rewrite -Hf add0r.
  + by rewrite -Hg addr0.
have fg_neq0 x : f x + g x != 0 by apply: lt0r_neq0.
exists (fun x => f x / (f x + g x)); split.
- move=> x; apply: (continuousM (cf x)).
  apply: continuous_comp; [exact/continuousD/cg/cf | exact: inv_continuous].
- rewrite E0.
  apply/seteqP; split => x /=; first by move->; rewrite mul0r.
  move/(f_equal (GRing.mul ^~ (f x + g x))).
  by rewrite -mulrA mulVf // mulr1 mul0r.
- rewrite F0.
  apply/seteqP; split => x /=.
    rewrite -{1}(addr0 (f x)) => <-; exact: mulfV.
  move/(f_equal (GRing.mul ^~ (f x + g x))).
  rewrite -mulrA mulVf // mulr1 mul1r => /eqP.
  by rewrite addrC -subr_eq subrr eq_sym => /eqP.
- move=> _ [x] _ /= <-.
  have fgx : (f x + g x)^-1 >= 0 by apply/ltW; rewrite invr_gt0.
  by rewrite in_itv /= mulr_ge0 //= -(mulfV (fg_neq0 x)) ler_pM // lerDl.
Qed.

Lemma perfectly_normal_space01_normal_closed :
  perfectly_normal_space01 -> normal_space_closed.
Proof.
move=> pns01 E F cE cF EF.
case: (pns01 E F cE cF EF) => f [/continuousP /= cf E0 F1 Rf].
exists (f@^-1` `]-oo,1/2[).
exists (f@^-1` `]1/2,+oo[); split.
- exact: cf.
- exact: cf.
- apply/disj_setPRL.
  rewrite preimage_setC.
  apply: preimage_subset => x.
  rewrite /= !in_itv /= andbT => /ltW.
  by rewrite leNgt => /negP.
- rewrite E0.
  apply: preimage_subset => x /= ->.
  by rewrite in_itv /= ltr_pdivlMr.
- rewrite F1.
  apply: preimage_subset => x /= ->.
  by rewrite in_itv /= ltr_pdivrMr // mul1r ltr1n.
Qed.

Lemma perfectly_normal_space01_normal :
  perfectly_normal_space01 -> normal_space T.
Proof.
move=> pns01 A cA B /set_nbhsP[C] [oC AC CB].
case: (pns01 A (~` C) cA).
- by rewrite closedC.
- exact/disj_setPCl.
move=> f [/continuousP /= cf f0 f1 f01].
exists (f @^-1` `]-oo, 1/2]).
  apply/set_nbhsP.
  exists (f @^-1` `]-oo, 1/2[).
  split => //.
  - exact: cf.
  - by rewrite f0 => x /= ->; rewrite in_itv /=.
  - by apply: preimage_subset => x /=; rewrite !in_itv /= => /ltW.
apply: subset_trans CB.
have /closure_id <- : closed (f @^-1` `]-oo, (1 / 2)]).
  rewrite -openC preimage_setC setCitv /= set_itvE set0U; exact: cf.
rewrite -(setCK C) f1 => x /=.
rewrite in_itv /= leNgt.
apply: contraNnot => ->.
by rewrite ltr_pdivrMr // mul1r /= ltr1n.
Qed.

Let perfectly_normal_space_41 :
  perfectly_normal_space01 -> perfectly_normal_space_Gdelta.
Proof.
move=> pns01; split.
  exact: perfectly_normal_space01_normal.
move=> E cE.
have [] := pns01 _ _ cE closed0.
  by apply/disj_setPLR; rewrite setC0.
move=> f [cf f0 f1 f01].
exists (fun n => f @^-1` `]-oo, 1/n.+1%:R[).
  move=> n; move/continuousP: cf; exact.
rewrite f0.
apply/seteqP; split => x /= Hx.
  by move=> i _ /=; rewrite Hx in_itv /= divr_gt0.
case: (ltrgtP (f x) 0) => // fx.
  have : f x \notin range f.
    by rewrite f01 mem_setE in_itv /= negb_and -ltNge fx.
  move/negP; elim.
  by rewrite inE /=; exists x.
suff : False by [].
have /= := Hx (truncn (1 / f x)) I.
rewrite in_itv /=.
have /real_truncnS_gt := num_real (1 / f x).
rewrite -ltf_pV2; last first.
- by rewrite posrE divr_gt0.
- by rewrite posrE.
rewrite !div1r invrK => /lt_trans/[apply].
by rewrite ltxx.
Qed.

Theorem Vedenissoff_closed : perfectly_normal_space_Gdelta <-> perfectly_normal_space 0.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_23 perfectly_normal_space_34 perfectly_normal_space_41.
tauto.
Qed.

Theorem Vedenissoff_open : perfectly_normal_space_Gdelta <-> perfectly_normal_space' 0.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_23 perfectly_normal_space_34 perfectly_normal_space_41.
tauto.
Qed.

Theorem Vedenissoff01 : perfectly_normal_space_Gdelta <-> perfectly_normal_space01.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_23 perfectly_normal_space_34 perfectly_normal_space_41.
tauto.
Qed.

End perfectlynormalspace.
