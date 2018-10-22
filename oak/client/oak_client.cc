#include "asylo/util/logging.h"
#include "gflags/gflags.h"

DEFINE_string(server_address, "127.0.0.1:8888", "Address of the server to connect to");

int main(int argc, char** argv) {
  ::google::ParseCommandLineFlags(&argc, &argv, /*remove_flags=*/true);

  if (FLAGS_server_address.empty()) {
    LOG(QFATAL) << "Must supply a non-empty address with --server_address";
  }

  LOG(INFO) << "start";
}
