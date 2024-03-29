(* TEST *)

let rec tailcall4 a b c d =
  if a < 0
  then b
  else tailcall4 (a-1) (b+1) (c+2) (d+3)

let rec tailcall8 a b c d e f g h =
  if a < 0
  then b
  else tailcall8 (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)

let rec tailcall16 a b c d e f g h i j k l m n o p =
  if a < 0
  then b
  else tailcall16 (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)
                  (i+8) (j+9) (k+10) (l+11) (m+12) (n+13) (o+14) (p+15)

let rec tailcall32 a b c d e f g h i j k l m n o p
                   q r s t u v w x y z aa bb cc dd ee ff =
  if a < 0
  then b
  else tailcall32 (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)
                  (i+8) (j+9) (k+10) (l+11) (m+12) (n+13) (o+14) (p+15)
                  (q+16) (r+17) (s+18) (t+19) (u+20) (v+21) (w+22) (x+23)
                  (y+24) (z+25) (aa+26) (bb+27) (cc+28) (dd+29) (ee+30) (ff+31)

let indtailcall8 fn a b c d e f g h =
  fn a b c d e f g h

let indtailcall16 fn a b c d e f g h i j k l m n o p =
  fn a b c d e f g h i j k l m n o p

let rec muttailcall8 a b c d e f g h =
  if a < 0
  then b
  else auxtailcall8 (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)

and auxtailcall8 a b c d e f g h =
  muttailcall8 a b c d e f g h

let rec muttailcall16 a b c d e f g h i j k l m n o p =
  if a < 0
  then b
  else auxtailcall16 (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)
                     (i+8) (j+9) (k+10) (l+11) (m+12) (n+13) (o+14) (p+15)

and auxtailcall16 a b c d e f g h i j k l m n o p =
  muttailcall16 a b c d e f g h i j k l m n o p

let rec muttailcall32 a b c d e f g h i j k l m n o p
                   q r s t u v w x y z aa bb cc dd ee ff =
  if a < 0
  then b
  else auxtailcall32 (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)
                  (i+8) (j+9) (k+10) (l+11) (m+12) (n+13) (o+14) (p+15)
                  (q+16) (r+17) (s+18) (t+19) (u+20) (v+21) (w+22) (x+23)
                  (y+24) (z+25) (aa+26) (bb+27) (cc+28) (dd+29) (ee+30) (ff+31)

and auxtailcall32 a b c d e f g h i j k l m n o p
                  q r s t u v w x y z aa bb cc dd ee ff =
  muttailcall32 a b c d e f g h i j k l m n o p
                q r s t u v w x y z aa bb cc dd ee ff

(* regression test for PR#6441: *)
let rec tailcall16_value_closures a b c d e f g h i j k l m n o p =
  if a < 0
  then b
  else tailcall16_value_closures
         (a-1) (b+1) (c+2) (d+3) (e+4) (f+5) (g+6) (h+7)
         (i+8) (j+9) (k+10) (l+11) (m+12) (n+13) (o+14) (p+15)
and fs = [tailcall16_value_closures]

let _ =
  print_int (tailcall4 1000000 0 0 0); print_newline();
  print_int (tailcall8 1000000 0 0 0 0 0 0 0); print_newline();
  print_int (tailcall16 1000000 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  print_newline();
  print_int (tailcall32 1000000 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  print_newline();
  print_int (indtailcall8 tailcall8 10 0 0 0 0 0 0 0); print_newline();
  print_int (indtailcall16 tailcall16 10 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  print_newline();
  print_int (tailcall16_value_closures 1000000 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  print_newline();
  print_int (muttailcall8 1000000 0 0 0 0 0 0 0); print_newline();
  print_int (muttailcall16 1000000 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  print_newline();
  print_int (muttailcall32 1000000 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0);
  print_newline()
