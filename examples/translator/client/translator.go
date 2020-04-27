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

	"github.com/golang/glog"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"

	translator_pb "github.com/project-oak/oak/examples/translator/proto"
)

var (
	address = flag.String("address", "localhost:8080", "Address of the Oak application to connect to")
	caCert  = flag.String("ca_cert", "", "Path to the PEM-encoded CA root certificate")
)

func translate(ctx context.Context, client translator_pb.TranslatorClient, text, fromLang, toLang string) {
	glog.Infof("Translate %q from %q to %q", text, fromLang, toLang)
	req := translator_pb.TranslateRequest{Text: text, FromLang: fromLang, ToLang: toLang}
	rsp, err := client.Translate(ctx, &req)
	if err != nil {
		glog.Errorf("Could not perform Translate(%q, %q=>%q): %v", text, fromLang, toLang, err)
		return
	}
	glog.Infof("Response: %q", rsp.TranslatedText)
}

func main() {
	flag.Parse()
	ctx := context.Background()

	// Connect to the Oak Application.
	creds, err := credentials.NewClientTLSFromFile(*caCert, "")
	if err != nil {
		glog.Exitf("Failed to set up TLS client credentials from %q: %v", *caCert, err)
	}
	conn, err := grpc.Dial(*address, grpc.WithTransportCredentials(creds))
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
