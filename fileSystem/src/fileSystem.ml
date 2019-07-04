(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Vincent Tourneur <vincent.tourneur@inria.fr>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

open Exec_plugin.Coqstr
open Exec_plugin.Coqnum
open Exec_plugin.Extends
open Exec_plugin.Coqunit
open Unix
open Exec_plugin.Query
open Exec_plugin.Utils

let string_of_coqstr coqstr =
  Bytes.to_string (bytes_of_coqstr coqstr)

let path = ["FreeSpec"; "Stdlib"; "FileSystem"; "Definitions"]

(* Should go in util ------------------------------------------------------- *)

type n_constructor = N0_N | Npos_N

module Ind_N = struct
  module N =
    Inductive.Make(struct
        type constructor = n_constructor
        let type_name = "Z"
        let modlist = ["Coq"; "Numbers"; "BinNums"]
        let names = [("N0", N0_N); ("Npos", Npos_N)]
      end)
end

let fold_bits input fzero fiter flast init =
(* Fold over [input] bits, from the least to the most significant bit, using
   [init] as its initial value:
     - [fzero] is called if [input] is 0
     - [fiter] is called for the least significant bits
     - [flast] is called for the most significant bit *)
  if input == 0
  then fzero init
  else let rec fold_bit_aux input acc =
         let next = input lsr 1 in
         let bit = input land 1 == 1 in
         if next == 0
         then flast acc
         else fold_bit_aux next (fiter acc bit)
       in fold_bit_aux input init

let int_of_coqpositive =
  (* This function does not implement any special protection against integer
     overflow. Because Coq [positive] terms are not bounded, there is no
     guarantee that [int_of_coqpositive] will be equivalent to its argument. *)
  let rec of_coqpositive_aux acc depth p =
    let (p, args) = app_full p in
    match (Ind.Positive.constructor_of p, args) with
    | (Some XH_positive, []) -> acc + depth
    | (Some XO_positive, [next]) -> of_coqpositive_aux acc (2 * depth) next
    | (Some XI_positive, [next]) -> of_coqpositive_aux (acc + depth) (2 * depth) next
    | _ -> raise (UnsupportedTerm "not a constructor of [positive]")
  in of_coqpositive_aux 0 1

let int_to_coqpositive i =
  let cXI = Ind.Positive.mkConstructor "xI" in
  let cXO = Ind.Positive.mkConstructor "xO" in
  let cXH = Ind.Positive.mkConstructor "xH" in
  let not_zero _ =
    raise (UnsupportedTerm "integer is not strictly positive") in
  let fiter cont bit =
    let c = if bit then cXI else cXO in
    fun next -> cont (Constr.mkApp (c, (Array.of_list [next]))) in
  let flast cont = cont cXH in
  fold_bits i not_zero fiter flast (fun x -> x)

let int_of_coqn n =
  let (n, args) = app_full n in
  match (Ind_N.N.constructor_of n, args) with
  | (Some N0_N, []) -> 0
  | (Some Npos_N, [p]) -> int_of_coqpositive p
  | _ -> raise (UnsupportedTerm "not a constructor of [N]")

let int_to_coqn = function
  | x when x > 0 -> Constr.mkApp (Ind_N.N.mkConstructor "Npos", Array.of_list [int_to_coqpositive x])
  | 0 -> Ind_N.N.mkConstructor "N0"
       | x -> raise (UnsupportedTerm "not a natural number")

(* ------------------------------------------------------------------------- *)

type mode_constructor = ReadOnly | WriteOnly | ReadWrite
type seekRef_constructor = Beginning | Current | End
type fileKind_constructor = Reg | Dir | Chr | Blk | Lnk | Fifo | Sock
type stats_constructor = MkStats
type options_constructor = DontCreate | DontCreateTruncate | MayCreate | MayCreateTruncate | MustCreate

module Ind_fs = struct
  module Mode =
    Inductive.Make(struct
        type constructor = mode_constructor
        let type_name = "mode"
        let modlist = path
        let names = [("ReadOnly", ReadOnly); ("WriteOnly", WriteOnly); ("ReadWrite", ReadWrite)]
      end)

  module SeekRef =
    Inductive.Make(struct
        type constructor = seekRef_constructor
        let type_name = "seekRef"
        let modlist = path
        let names = [("Beginning", Beginning); ("Current", Current); ("End", End)]
      end)

  module FileKind =
    Inductive.Make(struct
        type constructor = fileKind_constructor
        let type_name = "fileKind"
        let modlist = path
        let names = [("Reg", Reg); ("Dir", Dir); ("Chr", Chr); ("Blk", Blk); ("Lnk", Lnk); ("Fifo", Fifo); ("Sock", Sock)]
      end)
  module Stats =
    Inductive.Make(struct
        type constructor = stats_constructor
        let type_name = "stats"
        let modlist = path
        let names = [("MkStats", MkStats)]
      end)
  module Options =
    Inductive.Make(struct
        type constructor = options_constructor
        let type_name = "options"
        let modlist = path
        let names = [("DontCreate", DontCreate); ("DontCreateTruncate", DontCreateTruncate); ("MayCreate", MayCreate); ("MayCreateTruncate", MayCreateTruncate); ("MustCreate", MustCreate)]
      end)
end

let create_open_flags_list m c =
  let coqmode_to_open_flag_l m =
    let (m, args) = app_full m in
    match (Ind_fs.Mode.constructor_of m, args) with
    | (Some ReadOnly, []) -> [O_RDONLY]
    | (Some WriteOnly, []) -> [O_WRONLY]
    | (Some ReadWrite, []) -> [O_RDWR]
    | _ -> raise (UnsupportedTerm "not a constructor of [FileSystem.mode]") in
  let coqbool_create_to_open_flag_l c =
    let (c, args) = app_full c in
    match (Ind_fs.Options.constructor_of c, args) with
    | (Some DontCreate, []) -> []
    | (Some DontCreateTruncate, []) -> [O_TRUNC]
    | (Some MayCreate, []) -> [O_CREAT]
    | (Some MayCreateTruncate, []) -> [O_CREAT; O_TRUNC]
    | (Some MustCreate, []) -> [O_CREAT; O_EXCL]
    | _ -> raise (UnsupportedTerm "not a constructor of [bool]") in
  (coqmode_to_open_flag_l m) @ (coqbool_create_to_open_flag_l c)

let coqseekRef_to_seek_command ref =
  let (ref, args) = app_full ref in
  match (Ind_fs.SeekRef.constructor_of ref, args) with
  | (Some Beginning, []) -> SEEK_SET
  | (Some Current, []) -> SEEK_CUR
  | (Some End, []) -> SEEK_END
  | _ -> raise (UnsupportedTerm "not a constructor of [FileSystem.seekRef]")

let coqfileKind_of_file_kind = function
  | S_REG -> Ind_fs.FileKind.mkConstructor "Reg"
  | S_DIR -> Ind_fs.FileKind.mkConstructor "Dir"
  | S_CHR -> Ind_fs.FileKind.mkConstructor "Chr"
  | S_BLK -> Ind_fs.FileKind.mkConstructor "Blk"
  | S_LNK -> Ind_fs.FileKind.mkConstructor "Lnk"
  | S_FIFO -> Ind_fs.FileKind.mkConstructor "Fifo"
  | S_SOCK -> Ind_fs.FileKind.mkConstructor "Sock"

let coqz_to_fd : Constr.constr -> file_descr =
  fun z -> Obj.magic (int_of_coqz z)
let coqz_to_dh : Constr.constr -> dir_handle =
  fun z -> Obj.magic (int_of_coqz z)

let stats_to_coqstats s =
 Constr.mkApp ((Ind_fs.Stats.mkConstructor "MkStats"),
         (Array.of_list [int_to_coqz s.st_dev; int_to_coqz s.st_ino;
                         coqfileKind_of_file_kind s.st_kind; int_to_coqz s.st_perm;
                         int_to_coqz s.st_nlink; int_to_coqz s.st_uid;
                         int_to_coqz s.st_gid; int_to_coqz s.st_rdev;
                         int_to_coqn s.st_size]))

let install_interface =
  let stat = function
    | [str] -> stats_to_coqstats (stat (string_of_coqstr str))
    | _ -> assert false in
  let open_ = function
    | [m; o; str] -> int_to_coqz (Obj.magic
                                  (openfile
                                   (string_of_coqstr str)
                                   (create_open_flags_list m o)
                                   0o640))
    | _ -> assert false in
  let openDir = function
    | [str] -> int_to_coqz (Obj.magic (opendir (string_of_coqstr str)))
    | _ -> assert false in
  let fStat = function
    | [fd] -> stats_to_coqstats (fstat (coqz_to_fd fd))
    | _ -> assert false in
  let getSize = function
    | [fd] -> int_to_coqn (fstat (coqz_to_fd fd)).st_size
    | _ -> assert false in
  let read = function
    | [n; fd] -> let buff = Bytes.create (int_of_coqn n) in
               ignore (read (coqz_to_fd fd) buff 0 (int_of_coqn n));
               bytes_to_coqstr buff
    | _ -> assert false in
  let readDir = function
    | [dh] -> string_to_coqstr (readdir (coqz_to_dh dh))
    | _ -> assert false in
  let write = function
    | [str; fd] -> let buff = bytes_of_coqstr str in
                 ignore (write (coqz_to_fd fd) buff 0 (Bytes.length buff));
                 coqtt
    | _ -> assert false in
  let seek = function
    | [ref; n; fd] -> ignore (lseek (coqz_to_fd fd) (int_of_coqz n)
                                    (coqseekRef_to_seek_command ref));
                      coqtt
    | _ -> assert false in
  let close = function
    | [fd] -> close (coqz_to_fd fd);
               coqtt
    | _ -> assert false in
  let closeDir = function
    | [dh] -> closedir (coqz_to_dh dh);
               coqtt
    | _ -> assert false in
  let unlink = function
    | [str] -> unlink (string_of_coqstr str);
                coqtt
    | _ -> assert false in
  register_interface path [("Stat", stat); ("Open", open_); ("OpenDir", openDir);
                           ("FStat", fStat); ("GetSize", getSize); ("Read", read);
                           ("ReadDir", readDir); ("Write", write); ("Seek", seek);
                           ("Close", close); ("CloseDir", closeDir); ("Unlink", unlink)]
