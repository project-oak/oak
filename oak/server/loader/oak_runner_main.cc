/*
 * Copyright 2018 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <cstdlib>
#include <sstream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "oak/common/logging.h"
#include "oak/common/utils.h"
#include "oak/server/loader/oak_loader.h"

ABSL_FLAG(std::string, application, "", "Application configuration file");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");
ABSL_FLAG(std::string, private_key, "", "Path to the private key");
ABSL_FLAG(std::string, private_key_env, "OAK_TLS_PRIVATE_KEY",
          "Name of environment variable providing the path to the private key");
ABSL_FLAG(std::string, cert_chain, "", "Path to the PEM-encoded certificate chain");

std::shared_ptr<grpc::ServerCredentials> BuildTlsCredentials(std::string pem_root_certs,
                                                             std::string private_key,
                                                             std::string cert_chain) {
  grpc::SslServerCredentialsOptions::PemKeyCertPair key_cert_pair = {private_key, cert_chain};
  grpc::SslServerCredentialsOptions options;
  options.pem_root_certs = pem_root_certs;
  options.pem_key_cert_pairs.push_back(key_cert_pair);
  return grpc::SslServerCredentials(options);
}

int main(int argc, char* argv[]) {
  absl::ParseCommandLine(argc, argv);

  // Create loader instance.
  std::unique_ptr<oak::OakLoader> loader = absl::make_unique<oak::OakLoader>();

  // Load application configuration.
  std::unique_ptr<oak::ApplicationConfiguration> application_config =
      oak::ReadConfigFromFile(absl::GetFlag(FLAGS_application));

  std::string private_key_path = absl::GetFlag(FLAGS_private_key);
  std::string private_key_env = absl::GetFlag(FLAGS_private_key_env);
  if (private_key_path.empty() && !private_key_env.empty()) {
    const char* env_path = std::getenv(private_key_env.c_str());
    if (env_path) {
      private_key_path = env_path;
    }
  }
  if (private_key_path.empty()) {
    OAK_LOG(FATAL) << "No private key file specified.";
  }
  std::string cert_chain_path = absl::GetFlag(FLAGS_cert_chain);
  if (cert_chain_path.empty()) {
    OAK_LOG(FATAL) << "No certificate chain file specified.";
  }
  std::string private_key = oak::utils::read_file(private_key_path);
  std::string cert_chain = oak::utils::read_file(cert_chain_path);
  std::string ca_cert_path = absl::GetFlag(FLAGS_ca_cert);
  std::string ca_cert = ca_cert_path == "" ? "" : oak::utils::read_file(ca_cert_path);

  std::shared_ptr<grpc::ServerCredentials> grpc_credentials =
      BuildTlsCredentials(ca_cert, private_key, cert_chain);

  grpc::Status status = loader->CreateApplication(*application_config, grpc_credentials);
  if (!status.ok()) {
    OAK_LOG(ERROR) << "Failed to create application";
    return 1;
  }
  std::stringstream address;
  address << "0.0.0.0:" << application_config->grpc_port();
  OAK_LOG(INFO) << "Oak Application: " << address.str();

  // Wait (same as `sleep(86400)`).
  absl::Notification server_timeout;
  server_timeout.WaitForNotificationWithTimeout(absl::Hours(24));

  loader->TerminateApplication();

  return 0;
}
