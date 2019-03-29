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

Require Import FreeSpec.Stdlib.Console.
Require Import FreeSpec.Stdlib.FileSystem.
Require Import FreeSpec.Program.
Require Import Prelude.Control.

Local Open Scope prelude_scope.

Definition cat {ix} `{Use Console.i ix} `{Use FileSystem.i ix} : Program ix unit :=
  fd <- FileSystem.open FileSystem.ReadOnly FileSystem.N "Cat.v";
  size <- FileSystem.getSize fd;
  FileSystem.read size fd >>= Console.echo;;
  FileSystem.close fd.

Exec cat.
