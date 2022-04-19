#!/usr/bin/env python3

# Copyright 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
import os
import sys
import yaml
import http.client
import json

pipeline = {'steps': [
    {'label': 'trigger-build-resources',
     'trigger': 'vmm-reference-build-resources',
     'skip': 'No changes in resources or not a Pull Request'}
]}

pull_request = os.environ.get('BUILDKITE_PULL_REQUEST')
# the isnumeric() check is needed because the value
# will be 'false' if it's not a pull requests. See
# https://buildkite.com/docs/pipelines/environment-variables#bk-env-vars-buildkite-pull-request
if pull_request and pull_request.isnumeric():
    try:
        conn = http.client.HTTPSConnection("api.github.com", timeout=2)
        path = f"/repos/rust-vmm/vmm-reference/pulls/{pull_request}/files"
        conn.request('GET', path, headers={'user-agent': 'py.http/3'})
        content = conn.getresponse().read().decode('utf-8')
        for v in json.loads(content):
            if v['filename'].startswith('resources/'):
                pipeline['steps'][0]['skip'] = False
    except Exception as e:
        print(e, file=sys.stderr)

yaml.dump(pipeline, sys.stdout, sort_keys=False)
