# Logic Bot with Proof Visualization

This is a tool for logical reasoning and visualization of the proof search process. It can:

1. Validate logical arguments
2. Find proofs for valid arguments using automated reasoning
3. Visualize the recursive proof search process as a radial tree

## Installation

1. Clone the repository
2. Install dependencies:

```
pip install -r requirements.txt
```

## Usage

### Basic Usage

Run the script with built-in examples:

```
python logic_bot.py
```

### Command Line Options

The logic bot supports several command-line options:

```
python logic_bot.py [file] [options]
```

Options:
- `--visualize`: Display an interactive visualization of the proof search process
- `--save FILE`: Save the visualization to a file (PNG format by default)
- `--example N`: Run a specific example (1-3) instead of all examples

Examples:

```bash
# Run with visualization
python logic_bot.py --visualize

# Run a specific example with visualization
python logic_bot.py --example 2 --visualize

# Process proofs from a file and save visualizations
python logic_bot.py example_proofs.txt --visualize --save proofs.png
```

### Creating Proof Files

Create a text file with proofs in the following format:

```
PROOF: Example 1
PREMISE: p --> q
PREMISE: p
CONCLUSION: q

PROOF: Another Example
PREMISE: a | b
PREMISE: !a
CONCLUSION: b
```

## Visualization Features

The visualization shows:

- The branching proof search tree radiating from the center
- Successful rule applications in green
- Failed rule applications in red
- Statistics about the search process

## How It Works

1. The logic bot parses logical expressions into abstract syntax trees
2. It applies logical inference rules recursively to find a proof
3. The visualizer tracks all rule applications and their results
4. A radial tree graph is generated showing the entire proof search process

The visualization helps understand:
- Which rules were tried
- Where backtracking occurred
- Which paths led to successful proofs
- The overall complexity of the search 