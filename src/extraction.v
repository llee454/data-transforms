Require Coq.extraction.Extraction.
Require Import List.
Require Import Strings.String.
Require Import transform.

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Constant fst => "fst".

Extract Constant snd => "snd".

Extraction Inline fst snd.

Extract Inductive list => "list" ["[]" "(fun (x, xs) -> List.cons x xs)"]
  "(fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)".

Extract Constant app => "List.append".

Extraction Inline app.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive bool => "bool" ["true" "false"]
  "(fun branch0 branch1 b ->
     match b with
     | true -> branch0 ()
     | false -> branch1 ())".

Extract Constant negb => "Bool.not".

Extract Constant String.eqb => "String.equal".

Extract Inductive string => "string" ["" "UNDEFINED_TERM"].

Extract Constant existsb => "(fun f xs -> Core_kernel.List.exists xs ~f)".

Extract Constant filter => "(fun f xs -> Core_kernel.List.filter xs ~f)".

(*
Extract Constant sechash_t => "Analytics_aux.Sechash.t".

Extract Constant sechash_eqb => "Analytics_aux.Sechash.equal".

Extract Inductive laso_t => "Laso.t"
  ["(fun name_hash hs ->
    let name_address_hashes = Sechash.Set.of_list hs in
    Laso.Fields_of_laso_t.create
      ~name_hashe ~name_address_hashes ~city:{||} ~zip:0 ~age:0
      ~age_is_approximate:None ~gender:{||} ~ethnicity:{||} ~race:{||})"]
  "(fun branch0 x ->
    match x with
    | Laso.{name_hash; name_address_hashes; _} ->
      branch0 name_hash (Analytics_aux.Sechash.Set.to_list name_address_hashes))". *)

Extraction "transform" Filter_unique Join Alist.
