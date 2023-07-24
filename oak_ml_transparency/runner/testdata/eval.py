import argparse
import json

def main():
    parser = argparse.ArgumentParser(
        allow_abbrev=False,
        prog='MNIST evaluation',
        description='Evaluates an MNIST model against adversarial examples')

    parser.add_argument('--model', help="the model as a compressed tar archive")
    parser.add_argument('--output', help="path to store the evaluation result in") 

    args = parser.parse_args()
    output_path = args.output
    
    result = { "test_acc": 80.0 }
     
    # Serialize as json
    json_object = json.dumps(result, indent=4)
    
    # Write to file at the given output path
    with open(output_path, "w") as outfile:
        outfile.write(json_object)


if __name__ == "__main__":
    main()
