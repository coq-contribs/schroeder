(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                               Feb 2nd 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                             Equipollence.v                               *)
(****************************************************************************)

Require Import Ensembles.    (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.  (* Relation *)
Require Import Functions.

(************************************************************************)
(*         Equipollence and relation "is of cardinal less than"         *)

Section Equipollence.

Variable U : Type.
Variable A B : Ensemble U.
Let Rela := Relation U.

Inductive equipollence : Prop :=
    equipollence_intro : forall f : Rela, bijection U A B f -> equipollence.

Inductive inf_card : Prop :=
    inf_card_intro : forall f : Rela, injection U A B f -> inf_card.

End Equipollence.

(* $Id$ *)