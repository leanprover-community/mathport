/*
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
*/
#include <lean/lean.h>
#include <utility>

using namespace std;

namespace lean {
  void set_max_heartbeat(size_t max);

  extern "C" lean_object *lean_set_max_heartbeat(size_t max) {
    set_max_heartbeat(max);
    return lean_io_result_mk_ok(lean_box(0));
  }
}
