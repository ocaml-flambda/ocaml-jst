(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Typedtree

type unique_seen_reason =
  | Seen_as of Ident.t
  (* Stores for each unique identifier that has already been seen,
     the last expression where it (or one of its parents/aliases) has been seen.
     We also keep the identifier (e.g. itself, alias or parent) that we saw. *)
  | Tuple_match_on_aliased_as of Ident.t * Ident.t
  (* We do mark idents as seen if they are directly matched on.
     E.g. match x, y with ... -> x, y not seen
          match f x with ...  -> x seen

     But in the special case match x, y with | z -> ..., we end up using x, y
     in a newly-created tuple. In that case, we retroactively mark x and y
     as seen. *)

type unique_error =
  | Seen_twice of Ident.t * expression * unique_seen_reason * unique_seen_reason
  (* Record that we have seen an ident twice. The expression gives the
     other point where the identifier was seen. *)
  | Not_owned_in_expression of Ident.t
  (* Unique variables can not be used as free variables of closures,
     inside for-loops and while-loops. *)

exception Unique_error of Location.t * Env.t * unique_error

(* Check that idents which are used more than once, are not used with mode unique. *)
val check_uniqueness_exp : expression -> unit

(* Check that idents which are used more than once, are not used with mode unique. *)
val check_uniqueness_value_bindings : value_binding list -> unit
