# A bazel creds_helper script that provides gcloud authentication

# Since we can't echo anything to debug without breaking the script, this helps
# with any debugging needs.
function log () {
    echo "$1" >> /tmp/oci_auth.log
}

# Parse the input provided from bazel.
input=$(cat)
uri=$(jq -r ".uri" <<< $input)
host="$(echo $uri | awk -F[/:] '{print $4}')"

# Get a token from gcloud. You'll need to be authenticated.
TOKEN=$(gcloud auth application-default print-access-token)

# It's expected that this script echos a result with this format.
echo "{headers:{\"Authorization\": [\"Bearer $TOKEN\"]}}"
