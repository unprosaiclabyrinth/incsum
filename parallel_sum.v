(*
    Project - Proving correctness of list sum with concurrent modification
    Course: CS 472, Spring 2024, UIC
    Author: Himanshu Dongre
*)
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
Section proof.
Context `{!heapGS Σ}.

(**
  is_list
  Representation predicate in separation logic for a list of integers.
*)
Fixpoint is_list (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝ (* null pointer *)
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ v' : val, p ↦ (#x, v') ∗ is_list l' v'
  end.

Notation NULL := (InjLV #()).

  (* list sum *)

(**
  sum_list_coq
  Coq-level list sum function
*)
Fixpoint sum_list_coq (l : list Z) :=
  match l with
  | [] => 0%Z
  | h :: t => (h + sum_list_coq t)%Z
  end.

(**
  sum_list
  HeapLang list sum function.
*)
Definition sum_list : val :=
  rec: "sum_list" "l" :=
    match: "l" with
      NONE => #0
    | SOME "p" =>
      let: "h" := Fst !"p" in
      let: "t" := Snd !"p" in
      "h" + "sum_list" "t"
    end.

(**
  sum_list_spec
*)
Lemma sum_list_spec l v :
  {{{ is_list l v }}} sum_list v
  {{{ RET #(sum_list_coq l); is_list l v }}}.
Proof.
  iIntros (Φ) "Hl Post".
  iLöb as "IH" forall (l v Φ).
  destruct l as [|x l]; simpl; wp_rec.
  + iDestruct "Hl" as %->. wp_match. by iApply "Post".
  + iDestruct "Hl" as (p -> v) "[Hp Hl]". wp_match.
    do 2 (wp_load; wp_proj; wp_let).
    wp_apply ("IH" with "Hl"). iIntros "Hl". wp_op.
    iApply "Post". eauto with iFrame.
Qed.

  (* list increase *)

(**
  inc_list
  A function that increases all elements of a list in-place.
*)
Definition inc_list : val :=
  rec: "inc_list" "n" "l" :=
    match: "l" with
      NONE => #()
    | SOME "p" =>
      let: "x" := Fst !"p" in
      let: "next" := Snd !"p" in
      "p" <- ("n" + "x", "next");;
      "inc_list" "n" "next"
    end.

(**
  inc_list_spec
*)
Lemma inc_list_spec n l v :
  {{{ is_list l v }}}
    inc_list #n v
  {{{ RET #(); is_list (map (Z.add n) l) v }}}.
Proof.
  iIntros (Ø) "Hl Hpost".
  iLöb as "IH" forall (n l v Ø).
  unfold inc_list. wp_rec. fold inc_list.
  destruct l as [| h t]; simpl.
  + iDestruct "Hl" as %->.
    wp_let. wp_match.
    iApply "Hpost". auto.
  + iDestruct "Hl" as (p -> v') "(Hp & Hv')".
    wp_let. wp_match.
    do 2 (wp_load; wp_proj; wp_let).
    wp_store.
    wp_apply ("IH" with "[$Hv']").
    iIntros "H". iApply "Hpost". iFrame. auto.
Qed.

  (* spinlock *)

Definition try_acquire : val := λ: "l",
  CAS "l" #false #true.

Definition acquire : val :=
  rec: "acquire" "l" :=
    if: try_acquire "l" then #() else "acquire" "l".

Definition release : val := λ: "l",
  "l" <- #false.

Definition newlock : val := λ: <>,
  ref #false.

(**
  lock_inv
*)
Definition lock_inv (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ b : bool, l ↦ #b ∗ if b then True else R)%I.

Definition lockN : namespace := nroot .@ "lock".

(**
  is_lock
*)
Definition is_lock (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜ lk = #l ⌝ ∧ inv lockN (lock_inv l R))%I.

(**
  newlock_spec
*)
Lemma newlock_spec (R : iProp Σ):
  {{{ R }}} newlock #() {{{ lk, RET lk; is_lock lk R }}}.
Proof.
  iIntros (Φ) "HR HΦ".
  wp_lam. wp_alloc l as "Hl".
  iMod (inv_alloc lockN _ (lock_inv l R) with "[HR Hl]") as "#Hinv".
  { iNext. unfold lock_inv. iExists false. iFrame. }
  iModIntro. iApply "HΦ". unfold is_lock. iExists l. eauto.
Qed.

(**
  try_acquire_spec
*)
Lemma try_acquire_spec lk R :
  {{{ is_lock lk R }}} try_acquire lk
  {{{ b, RET #b; if b is true then R else True }}}.
Proof.
  iIntros (Φ) "#Hl HΦ".
  unfold is_lock.
  iDestruct "Hl" as (l ->) "#Hinv".
  wp_rec.
  wp_bind (CmpXchg _ _ _).
  iInv lockN as (b) "[Hl HR]" "Hclose".
  destruct b.
  + wp_cmpxchg_fail. iMod ("Hclose" with "[Hl]") as "_".
    - iNext. iExists true. iFrame.
    - iModIntro. wp_proj.
      iApply "HΦ". done.    
  + wp_cmpxchg_suc.
    iMod ("Hclose" with "[$Hl]") as "_".
    iModIntro. wp_proj.
    iApply "HΦ". done.
Qed.

(**
  acquire_spec
*)
Lemma acquire_spec lk R :
  {{{ is_lock lk R }}} acquire lk {{{ RET #(); R }}}.
Proof.
  iIntros (Φ) "#Hl Hpost".
  iLöb as "IH".
  wp_rec.
  wp_apply (try_acquire_spec with "Hl").
  iIntros (b) "HR".
  destruct b.
  - wp_if_true.
    iApply "Hpost"; auto.
  - wp_if_false.
    wp_apply "IH".
    auto.
Qed.

(**
  release_spec
*)
Lemma release_spec lk R :
  {{{ is_lock lk R ∗ R }}} release lk {{{ RET #(); True }}}.
Proof.
  iIntros (Ø) "(#Hpre & HR) Hpost".
  unfold is_lock.
  iDestruct "Hpre" as (l ->) "#Hinv".
  unfold release. wp_lam. Fail wp_store.
  iInv lockN as (b) "[H1 H2]" "Hclose".
  wp_store.
  iMod ("Hclose" with "[$H1 HR]"); auto.
  iApply "Hpost". done.
Qed.

  (* parallel inc sum *)

Definition parallel_inc_sum_locked (lock : val): val := λ: "n" "v",
  let: "sum" := ref #0 in
  ((acquire lock;; inc_list "n" "v";; release lock) |||
  (acquire lock;; "sum" <- (sum_list "v");; release lock));;
  !"sum".

Definition inc_sum_inv (n : Z) (l : list Z) (v : val) :=
  (∃ (l' : list Z), ⌜(sum_list_coq l ≤ sum_list_coq l')%Z⌝ ∗ is_list l' v)%I.

Definition incsumN : namespace := nroot .@ "incsum".

Lemma sum_inc_eq_n_len : forall (l : list Z) n,
  (sum_list_coq (map (Z.add n) l) = (n * length l) + sum_list_coq l)%Z.
Proof.
  intros l n. induction l as [| h t IH]; simpl; lia.
Qed.      

Lemma parallel_inc_sum_locked_spec lock l v (n : Z) :
  {{{ is_lock lock (inc_sum_inv n l v) ∗ ⌜(0 ≤ n)%Z⌝ }}}
    parallel_inc_sum_locked lock #n v
  {{{ m, RET #m; ⌜(sum_list_coq l ≤ m)%Z⌝ }}}.
Proof.
  iIntros (Ø) "(#Hl & %Hn) Hpost".
  unfold parallel_inc_sum_locked. wp_lam. wp_let.
  wp_alloc sum as "Hsum". wp_let.
  wp_bind ((acquire lock;; inc_list #n v;; release lock) ||| (acquire lock;; #sum <- sum_list v;; release lock))%E.
  wp_smart_apply ((wp_par (fun _ => True)%I (fun _ => (∃ (m : Z), ⌜(sum_list_coq l ≤ m)%Z⌝ ∗ sum ↦ #m))%I) with "[] [Hsum]").
  + wp_apply (acquire_spec with "[Hl]").
    - unfold is_lock. iDestruct "Hl" as (l0) "[%Hl0 Hinv]".
      iExists l0. iSplit.
      { iPureIntro. done. }
      { done. }
    - iIntros "HR". wp_seq.
      unfold inc_sum_inv. 
      iDestruct "HR" as (l') "(%H1 & Hl')".
      wp_apply (inc_list_spec with "Hl'").
      iIntros "H". wp_seq.
      wp_apply (release_spec with "[$Hl H]").
      { iExists (map (Z.add n) l'). iSplit.
        { iPureIntro.
          rewrite sum_inc_eq_n_len.
          lia. }
        { done. }}
      { done. }
  + wp_apply (acquire_spec with "[Hl]"). done.
    iIntros "H". wp_seq.
    unfold is_lock. iDestruct "Hl" as (l0) "(%Hlock & Hinv)". subst.
    unfold inc_sum_inv. iDestruct "H" as (l') "(%H1 & Hl')".
    wp_apply (sum_list_spec with "[Hl']"). done.
    iIntros "Hl'". wp_store.
    wp_apply (release_spec with "[Hl']").
    - iSplitR.
      { unfold is_lock. iExists l0. iSplit; done. }
      { iExists l'. iFrame. done. }
    - iIntros "_". iExists (sum_list_coq l'). iFrame. done.
  + iIntros (v1 v2) "[_ Hm]".
    iDestruct "Hm" as (m) "[%H1 Hm]".
    iNext. wp_pure _. wp_lam. wp_load.
    iApply "Hpost". unfold is_lock. done. Unshelve.       

Admitted.