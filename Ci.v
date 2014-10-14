Require Import List.

Fixpoint SerialMerge (eat: list nat -> bool) branch input_commits :=
  match input_commits with
    | nil => branch
    | h :: t =>
      match eat (h :: branch) with
        | false => SerialMerge eat branch t
        | true => SerialMerge eat (h :: branch) t
      end
  end.

Lemma AllSerialMergeOk: forall (eat: list nat -> bool) (branch commits: list nat),
  eat branch = true -> eat (SerialMerge eat branch commits) = true.
Proof. Admitted.

Lemma LengthNextLt: forall (a n: nat) (tl: list nat),
  length (a :: tl) <= S n -> length tl <= n.
Proof.
intros.
destruct tl.
simpl. apply Le.le_0_n.
simpl.
assert (H4: length (a:: n0 :: tl) = S (S (length tl))).
simpl.
reflexivity.
rewrite H4 in H.
apply Le.le_S_n in H.
apply H.
Qed.

Lemma AllSerialMergeOk_size: forall (eat: list nat -> bool) (branch: list nat) (commits: list nat) (n:nat),
  length commits <= n /\ eat branch = true -> eat (SerialMerge eat branch commits) = true.
Proof.
intros.
induction n.
assert (H3: commits = nil).
inversion H.
inversion H0.
destruct commits.
reflexivity.
inversion H3.
rewrite H3.
unfold SerialMerge.
inversion H.
apply H1.
inversion H.
clear H.
inversion H0.
Focus 2.
apply IHn.
apply conj.
apply H2.
apply H1.
Focus 1.
clear H0.
induction commits.
inversion H2.
clear IHn.
unfold SerialMerge.
destruct (eat (a::branch)).
Focus 2.
apply IHcommits.
Focus 2.
inversion H2.
simpl.
(* we arrive at False *)
Admitted.

(*(* now the overall reccursion *)
induction commits.
(* commit = nil *)
apply IHn.
destruct H.
split.
simpl.
apply Le.le_0_n.
apply H0.
(* commit = hd :: tail *)
inversion H.
apply LengthNextLt in H0.
unfold SerialMerge.
destruct (eat (a :: branch)).
Focus 2.
apply IHcommits.
apply conj.
apply le_S.
apply H0.
apply H1.
intros.
inversion H2.
apply IHcommits.
apply conj.
apply le_S.
apply H0.
apply H1.

(*assert (H5: eat (SerialMerge eat branch commits) = true).
apply IHcommits.
apply conj.
apply le_S.
apply H0.
apply H1.
intros.*) *)
