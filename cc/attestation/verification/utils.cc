/*
 * Copyright 2023 The Project Oak Authors
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

#include "cc/attestation/verification/utils.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cc/utils/cose/cwt.h"
#include "proto/attestation/eventlog.pb.h"
#include "proto/attestation/evidence.pb.h"
#include "proto/attestation/verification.pb.h"

namespace oak::attestation::verification {

namespace {
using ::oak::attestation::v1::ContainerLayerData;
using ::oak::attestation::v1::Event;
using ::oak::attestation::v1::Evidence;
using ::oak::utils::cose::Cwt;
}  // namespace

absl::StatusOr<std::string> ExtractPublicKey(absl::string_view certificate) {
  auto cwt = Cwt::Deserialize(certificate);
  if (!cwt.ok()) {
    return cwt.status();
  }
  auto public_key = cwt->subject_public_key.GetPublicKey();
  return std::string(public_key.begin(), public_key.end());
}

absl::StatusOr<ContainerLayerData> ExtractContainerLayerData(
    const Evidence& evidence) {
  if (evidence.event_log().encoded_events_size() == 3) {
    auto encoded_event = evidence.event_log().encoded_events(2);
    Event event;
    if (!event.ParseFromString(encoded_event)) {
      return absl::InvalidArgumentError(
          "Failed to parse event from encoded event");
    }
    if (event.tag() == "ORCHESTRATOR") {
      ContainerLayerData container_layer_data;
      if (!event.event().UnpackTo(&container_layer_data)) {
        return absl::InvalidArgumentError(
            "Failed to parse container layer data from event");
      }
      return container_layer_data;
    }
  }
  return absl::NotFoundError("No container layer data found in event log");
}

absl::StatusOr<std::string> ExtractEncryptionPublicKey(
    const Evidence& evidence) {
  // Check whether the evidence is for Oak Containers. If so, we need to
  // extract the encryption public key from the event log.
  auto container_layer_data = ExtractContainerLayerData(evidence);
  if (container_layer_data.ok()) {
    return container_layer_data->hybrid_encryption_public_key();
  }
  if (container_layer_data.status().code() != absl::StatusCode::kNotFound) {
    return container_layer_data.status();
  }
  // Otherwise, we can extract the public key from the application keys
  // certificate.
  return ExtractPublicKey(
      evidence.application_keys().encryption_public_key_certificate());
}

absl::StatusOr<std::string> ExtractSigningPublicKey(const Evidence& evidence) {
  // Check whether the evidence is for Oak Containers. If so, we need to
  // extract the signing public key from the event log.
  auto container_layer_data = ExtractContainerLayerData(evidence);
  if (container_layer_data.ok()) {
    return container_layer_data->signing_public_key();
  }
  if (container_layer_data.status().code() != absl::StatusCode::kNotFound) {
    return container_layer_data.status();
  }
  // Otherwise, we can extract the public key from the application keys
  // certificate.
  return ExtractPublicKey(
      evidence.application_keys().signing_public_key_certificate());
}

}  // namespace oak::attestation::verification
