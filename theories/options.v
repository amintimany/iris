(** Coq configuration for Iris (not meant to leak to clients) *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

Export Set Default Proof Using "Type".
Export Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)

(* Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
Export Set Default Goal Selector "!".

(* "Fake" import to whitelist this file for the check that ensures we import
this file everywhere.
From iris Require Import options.
*)
