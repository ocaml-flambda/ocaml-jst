/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#ifndef CAML_ROOTS_H
#define CAML_ROOTS_H

#ifdef CAML_INTERNALS

#include "misc.h"
#include "memory.h"

typedef void (*scanning_action) (value, value *);

void caml_oldify_local_roots (void);
void caml_darken_all_roots_start (void);
intnat caml_darken_all_roots_slice (intnat);
void caml_do_roots (scanning_action, int);
extern uintnat caml_incremental_roots_count;
#ifndef NATIVE_CODE
CAMLextern void caml_do_local_roots_byt (scanning_action, value *, value *,
                                         struct caml__roots_block *);
#define caml_do_local_roots caml_do_local_roots_byt
#else
CAMLextern void caml_do_local_roots_nat (
                     scanning_action maj, scanning_action min,
                     char * c_bottom_of_stack,
                     uintnat last_retaddr, value * v_gc_regs,
                     struct caml__roots_block * gc_local_roots,
                     struct caml_local_arenas* local_arenas);
#define caml_do_local_roots caml_do_local_roots_nat
#endif

CAMLextern void (*caml_scan_roots_hook) (scanning_action);

#endif /* CAML_INTERNALS */

#endif /* CAML_ROOTS_H */
