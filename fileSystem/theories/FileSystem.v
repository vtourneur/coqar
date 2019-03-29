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

Require Import FreeSpec.Exec.
Require Export Coq.Strings.String.
Require Import FreeSpec.Program.
Require Import BinInt.

Module FileSystem.
  Inductive mode: Type :=
  | ReadOnly : mode
  | WriteOnly : mode
  | ReadWrite : mode.

  Inductive options: Type :=
  | N : options   (* The file must exist. *)
  | NT : options  (* The file must exist, and is emptied when opened.
                     The mode must allow writing. *)
  | Y : options   (* If the file does not exist, it is created. *)
  | YT : options  (* If the file does not exist, it is created.
                     If it exists, it is emptied when opened.
                     The mode must allow writing. *)
  | YY : options. (* The file must not exist, and it is created when opened. *)

  Inductive seekRef: Type :=
  | Beginning : seekRef
  | Current : seekRef
  | End : seekRef.

  Inductive fileKind: Type :=
  | Reg : fileKind
  | Dir : fileKind
  | Chr : fileKind
  | Blk : fileKind
  | Lnk : fileKind
  | Fifo : fileKind
  | Sock : fileKind.

  Record stats: Type := MkStats
  {
    dev : Z;
    ino : Z;
    kind : fileKind;
    perm : Z;
    nlink : Z;
    uid : Z;
    gid : Z;
    rdev : Z;
    size : Z;
  }.

  Inductive i: Type -> Type :=
  | Stat: string -> i stats
  | Open: mode -> options -> string -> i Z
  | OpenDir: string -> i Z
  | FStat: Z -> i stats
  | GetSize: Z -> i Z
  | Read: Z -> Z -> i string
  | ReadDir: Z -> i string
  | Write: string -> Z -> i unit
  | Seek: seekRef -> Z -> Z -> i unit
  | Close: Z -> i unit
  | CloseDir: Z -> i unit.

  Definition stat {ix} `{Use i ix} (str: string)
    : Program ix stats :=
    request (Stat str).

  Definition open {ix} `{Use i ix} (m: mode) (o: options) (str: string)
    : Program ix Z :=
    request (Open m o str).

  Definition openDir {ix} `{Use i ix} (str: string)
    : Program ix Z :=
    request (OpenDir str).

  Definition fStat {ix} `{Use i ix} (fd: Z)
    : Program ix stats :=
    request (FStat fd).

  Definition getSize {ix} `{Use i ix} (fd: Z)
    : Program ix Z :=
    request (GetSize fd).

  Definition read {ix} `{Use i ix} (n fd: Z)
    : Program ix string :=
    request (Read n fd).

  Definition readDir {ix} `{Use i ix} (dh: Z)
    : Program ix string :=
    request (ReadDir dh).

  Definition write {ix} `{Use i ix} (str: string) (fd: Z)
    : Program ix unit :=
    request (Write str fd).

  Definition seek {ix} `{Use i ix} (ref: seekRef) (n fd: Z)
    : Program ix unit :=
    request (Seek ref n fd).

  Definition close {ix} `{Use i ix} (fd: Z)
    : Program ix unit :=
    request (Close fd).

  Definition closeDir {ix} `{Use i ix} (dh: Z)
    : Program ix unit :=
    request (CloseDir dh).
End FileSystem.

Declare ML Module "stdlib_fileSystem_plugin".
