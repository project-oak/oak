// Copyright 2020 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package main

import (
	"context"
	"flag"
	"fmt"

	"github.com/golang/glog"
	"github.com/golang/protobuf/proto"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/status"

	translator_pb "github.com/project-oak/oak/examples/translator/proto"
	label_pb "github.com/project-oak/oak/oak_abi/proto/label"
)

var (
	address = flag.String("address", "localhost:8080", "Address of the Oak application to connect to")
	caCert  = flag.String("ca_cert", "", "Path to the PEM-encoded CA root certificate")
)

// Keep in sync with /oak/server/rust/oak_runtime/src/node/grpc/server/mod.rs.
const oakLabelGrpcMetadataKey = "x-oak-label-bin"

func translate(ctx context.Context, client translator_pb.TranslatorClient, text, fromLang, toLang string) {
	glog.Infof("Translate %q from %q to %q", text, fromLang, toLang)
	req := translator_pb.TranslateRequest{Text: text, FromLang: fromLang, ToLang: toLang}
	rsp, err := client.Translate(ctx, &req)
	if err != nil {
		rpcStatus, ok := status.FromError(err)
		if !ok {
			glog.Fatalf("Could not perform Translate(%q, %q=>%q): internal error %v", text, fromLang, toLang, err)
		}
		if rpcStatus.Code() != codes.NotFound {
			glog.Fatalf("Could not perform Translate(%q, %q=>%q): %v", text, fromLang, toLang, err)
		}
		glog.Errorf("Failed to Translate(%q, %q=>%q): not found", text, fromLang, toLang)
		return
	}
	glog.Infof("Response: %q", rsp.TranslatedText)
}

// TODO(#1097): move this into an SDK package to allow re-use.

type LabelMetadata struct {
	metadata map[string]string
}

func NewLabelMetadata(label label_pb.Label) (*LabelMetadata, error) {
	label_data, err := proto.Marshal(&label)
	if err != nil {
		return nil, fmt.Errorf("Failed to serialize label %v: %v", label, err)
	}
	return &LabelMetadata{
		metadata: map[string]string{
			oakLabelGrpcMetadataKey: string(label_data),
		},
	}, nil
}

// Implement the grpc.PerRPCCredentials interface.

func (lm *LabelMetadata) GetRequestMetadata(ctx context.Context, uri ...string) (map[string]string, error) {
	return lm.metadata, nil
}

func (lm *LabelMetadata) RequireTransportSecurity() bool {
	return true
}

func main() {
	flag.Parse()
	ctx := context.Background()

	// Connect to the Oak Application.
	creds, err := credentials.NewClientTLSFromFile(*caCert, "")
	if err != nil {
		glog.Exitf("Failed to set up TLS client credentials from %q: %v", *caCert, err)
	}
	// TODO(#1066): Use a more restrictive Label.
	label := label_pb.Label{}
	metadata, err := NewLabelMetadata(label)
	if err != nil {
		glog.Exitf("Failed to create label metadata for %v: %v", label, err)
	}
	conn, err := grpc.Dial(*address, grpc.WithTransportCredentials(creds), grpc.WithPerRPCCredentials(metadata))
	if err != nil {
		glog.Exitf("Failed to dial Oak Application at %v: %v", *address, err)
	}
	defer conn.Close()
	client := translator_pb.NewTranslatorClient(conn)

	// Perform multiple invocations of the same Oak Node, with different parameters.
	translate(ctx, client, "WORLDS", "en", "fr")
	translate(ctx, client, "WORLDS", "en", "it")
	translate(ctx, client, "WORLDS", "en", "cn")
	translate(ctx, client, "OSSIFRAGE", "en", "fr")
}
