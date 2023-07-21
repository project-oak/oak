# Oak ML Transparency

The goal of Oak ML Transparency is to generate non-forgeable claims about
machine learning models by evaluating them against an evaluation script in a
secure environment and embedding the result of the execution as a JSON object in
a claim generated and signed by the secure execution environment.

To the core of this design is a [runner](./runner) that runs the script and
generates the claim. For more details please see the linked documentation.

## The evaluation script

Currently, the runner can run an evaluation script that is a python script, and
accepts the following input flags:

- `--model`: input path in the local file system for loading the model
- `--output`: output path where the script stores the result of the evaluation

The result of the evaluation can be anything, but we recommend using a JSON
document, since the generated claim itself is a JSON object.

## The claim

For details about the claim, see the
[claim format](https://github.com/project-oak/transparent-release/blob/main/docs/claim-transparency.md)
proposed by our transparent-release project.
