(*
    Project - Proving mutual exclusion for lock algorithms
    Course: CS 472, Spring 2024, UIC
    Author: Himanshu Dongre
*)

From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.

Section proof.
  Context `{!heapGS Σ}.
  Context `{!spawnG Σ}.

(* TODO: Peterson's lock definition *)
Definition peterson_newlock : val := λ: "<>",
  AllocN #3 #false. 

(** 
public void lock() {
  int me = ThreadID.get();
  flag[me] = true;
  victim = me;
  while (there_exists_other(flag[other]) && victim == me) {
    // busy wait
  }
}
*)
Definition peterson_lock : val := λ: "me" "flags" "victim",
  CAS "victim" "victim" "me"
  CAS ("flag" + "me") #false #true
  if: 

Definition peterson_unlock : val. Admitted.

(* TODO: Peterson's lock spec(s)    *)

(* TODO: Definition of parallel count with 2 threads and Peterson's lock *)
(* Definition parallel_count_peterson_2 : val := Admitted.               *)
(* TODO: parallel_count_peterson_2 spec                                  *)
(** Show that {{ c = 0 }} parallel_count_peterson_2 {{ c = 2 }}          *)

(* TODO: Definition of parallel count with N (>2) threads and Peterson's lock *)
(* Definition parallel_count_peterson_N : val := Admitted.                    *)
(* TODO: parallel_count_peterson_N spec                                       *)
(** Disprove                                                                  *) (*?*)

(* TODO: Filter lock definition *) (*?*)
(* TODO: Filter lock spec(s)    *)

(* TODO: Definition of parallel count with N (>=2) threads and filter lock *)
(* Definition parallel_count_filter_N : val := Admitted.                   *)
(* TODO: parallel_count_filter_N spec                                      *)
(** Show that {{ c = 0 }} parallel_count_filter_N {{ c = N }}              *) (*?*)