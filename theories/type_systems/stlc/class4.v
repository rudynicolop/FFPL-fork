From stdpp Require Import base relations tactics.
From ffpl.lib Require Import prelude.
From ffpl.type_systems.stlc Require Import lang closed notation.

Lemma steps_plus_r (e1 e2 e2' : expr) :
  rtc step e2 e2' ->
  rtc step (e1 + e2)%E (e1 + e2')%E.
Proof. Admitted.

Lemma steps_plus_l (e1 e1' e2 : expr) :
  is_val e2 ->
  rtc step e1 e1' ->
  rtc step (e1 + e2)%E (e1' + e2)%E.
Proof. Admitted.

Lemma steps_app_r (e1 e2 e2' : expr) :
  rtc step e2 e2' ->
  rtc step (e1 e2) (e1 e2').
Proof. Admitted.

Lemma steps_app_l (e1 e1' e2 : expr) :
  is_val e2 ->
  rtc step e1 e1' ->
  rtc step (e1 e2) (e1' e2).
Proof. Admitted.

Lemma big_step_steps e v :
  big_step e v -> rtc step e v.
Proof. Admitted.
