#!/bin/bash

# This script applies the GNU GPL notice to all source files which should contain it.

copyright=$(cat << EOF
/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */

EOF
)

copyrightLattice=$(cat << EOF
# This file is part of the Property Checker.
# Copyright (c) 2021 -- present. Property Checker developers.
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License version 2 only, as
# published by the Free Software Foundation.
#
# This code is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# version 2 for more details.
#
# You should have received a copy of the GNU General Public License version
# 2 along with this work; if not, write to the Free Software Foundation,
# Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.

EOF
)

for file in $(find src -name '*.java'); do
  if ! grep -q "Copyright (c)" $file; then
    echo "$copyright" | cat - $file > __temp__ && mv __temp__ $file
  fi
done

for file in $(find tests -name '*.java'); do
  if ! grep -q "Copyright (c)" $file; then
    echo "$copyright" | cat - $file > __temp__ && mv __temp__ $file
  fi
done

for file in $(find tests -name 'lattice_*'); do
  if ! grep -q "Copyright (c)" $file; then
    echo "$copyrightLattice" | cat - $file > __temp__ && mv __temp__ $file
  fi
done

