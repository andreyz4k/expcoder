# ExpCoder

ExpCoder is a dynamic curriculum learning system that gradually learns to solve a given set of tasks over a number of iterations by using previously found solutions to expand the library of compositional abstract transformations and improve its guiding intuition that increases the probability of finding a solution on the next iteration. It is built on top of the ideas from [DreamCoder](https://github.com/ellisk42/ec) and improves upon it in several important ways.

Tasks are defined as program synthesis problems with sets of input and output examples. The system is tasked with finding a program that produces the desired outputs from the given input values and preferably generalizes to new similar inputs in a way that would feel natural to a human. One example of such a dataset would be the [ARC-AGI Benchmark](https://github.com/arcprize/ARC-AGI-2).

The system is provided with a starting library of available functions that should cover all required general-purpose primitives and some domain-specific methods for a specific set of tasks. This library is also referred to as grammar.

Solution programs are written in a custom dialect of parametrically-typed lambda calculus with a mix of De Bruijn indices and named variables. That allows extracting repeating patterns in found solutions and reusing them as new composite functions easily, and also provides a way to store specific intermediate data representations in the middle of the program. More on that later.

## Contents

- [How it works](#how-it-works)
- [Main Features](#main-features)
    - [Reversible functions](#reversible-functions)
    - [Reversible functions as abstract transformations](#reversible-functions-as-abstract-transformations)
    - [Bidirectional search](#bidirectional-search)
    - [Variables with multiple options or wildcards](#variables-with-multiple-options-or-wildcards)
    - [Guiding system](#guiding-system)
        - [Neural network architecture](#neural-network-architecture)
        - [Adding manually written solutions to the training data](#adding-manually-written-solutions-to-the-training-data)
        - [Using representation complexity](#using-representation-complexity)
    - [Learning new functions](#learning-new-functions)
- [Example solutions](#example-solutions)
- [Limitations](#limitations)
- [How to run](#how-to-run)
- [Acknowledgments](#acknowledgments)

## How it works

There are three main components of the system:

- Enumerator/solver that explores the space of possible programs for a given task using directions from the guiding model and validates their correctness.
- Compressor that searches for repeating patterns in the found solutions, saves them as new composite functions, adds them to the library, and rewrites the found solutions to use them.
- Guiding model that provides directions for the enumerator to explore the space of possible programs. It's not a generative model because its output is not code but a set of weights for library functions that serve as a sort of intuition that some functions are more likely to be useful for solving the current task.

The outer loop of the system looks a lot like the one in DreamCoder:

- First, the system tries to solve all the tasks using the current grammar and the guiding model.
- Then, the compressor searches for new useful composite functions, adds them to the grammar, and rewrites the found solutions to use them.
- After that, the guiding model goes through the training cycle using all the solutions found so far and the new grammar.
- The outer loop repeats for a given number of iterations.

The main difference from DreamCoder is that we don't have a "dreaming" phase because our changes to the language made dreaming up new meaningful programs way too difficult.

## Main Features

### Reversible functions

One of the main issues in DreamCoder and other top-down program synthesis systems is that it's impossible to check if a program is valid and can generate the desired output until the whole program is finished.
This can lead to cases where in one part of the program we already have an invalid but correctly typed expression, like attempting to extract an element from an empty list, but the other part of the program is not written yet, so the search process will continue to explore all possible ways to complete it, even though it's already doomed to fail.
Or it can generate a prototype that always generates output of the same size, goes on to explore what the elements could be, but the example outputs are of different sizes.

It doesn't affect the correctness of the found solutions, but it does affect how much time we spend exploring irrelevant search branches.
And since we are exploring an exponentially infinite space of all possible programs, every opportunity to prune invalid branches early can lead to a disproportionately large speedup.

This leads us to the idea of reversible functions. For these functions, we can predict what their input values would be that would produce the desired output value.
For example, if we have the function `cons` that appends an element to the end of a list, we can predict what would be the element and the input list that would produce the desired output list.
Or if we have the function `repeat` that repeats an element a given number of times, we can check if the given list can be generated by this function at all (not if it has different elements) and predict its input values.
It also works for higher-order functions, like `map` or `fold` - if their parameter function is reversible, then their combination is reversible as well.

What does it give us?
If we are running our top-down program search and our current partially written program is reversible, we can fill the gaps with variables and try running it in the reverse direction.
If it fails, we can drop this search branch altogether, but if it succeeds, we'll have new values for these new variables, and we can start exploring new search trees that aim to find programs that would produce these new values.

This change transforms the search space from one search tree to a tree of trees, where the nodes in the outer tree correspond to the variables, and they are connected by program blocks that are reversible, and the inner trees look like the original program search tree.

Additionally, since we have separate search trees for each variable, we can use different function weights in each of them, representing their usefulness for generating each specific variable value and type instead of using the same weights for the whole task, as is done in DreamCoder.

### Reversible functions as abstract transformations

When we talk about human cognition, we often talk about our ability to use abstractions.
One way to think about it is that when we are processing or "trying to make sense of" some incoming data, we are splitting it into some common patterns or categories and event-specific parameters that can be unique to this specific event.
For example, if I'm looking outside my window, I can say that I see a car that has a specific color, that is parked in a specific place, next to it there is a tree of a specific species, sidewalk of a specific material and width, and so on.
All these parameters combined represent all the information that I get from the image, but they are represented in a more structured way than what I got originally in the cones and rods of my eyes.

What is important here is that if we're operating in an idealized scenario where we don't have any noise and don't filter out any information, we can perfectly reconstruct the original data from the abstracted representation.
This is exactly what reversible functions allow us to do.
If we have a function that is reversible, we can use it to abstract the input data into a more structured representation, and then run it in reverse to reconstruct the original data from the abstracted representation.

So, if we have a system that learns more and more complex reversible functions, it essentially learns new ways to transform data into useful structured representations, which might be a necessary step for solving tasks that have complex underlying data structure.

### Bidirectional search

Going back to ARC, we can notice that often when a human tries to solve a task, they first try to understand what is going on in both the input and output grids, build abstract representations for them, and only then they try to connect one to another and explain their output representations using what they could find in the input representations.
If we are using the same mental models when decomposing input and output grids, can we make a program synthesis system that would do the same?

If we are writing a usual program for an ARC-like task, it would go roughly like this:

`input_grid to input_representation` -> `input_representation to output_representation` -> `output_representation to output_grid`

The first and the last steps would use two totally separate sets of methods - that's how most of the publicly available DSLs for ARC are designed.
But they represent the same set of abstract transformations; they are just applied in different directions.

This is where reversible functions come in. If we make one part of the solution program run in reverse direction, we can use the same set of functions for finding better abstract representations for both input and output grids.

What part gets reversed? Since each program block is built in a top-down manner, with its "top" being the output, and the only starting points are the input and output grids, we can only reverse the first part of the program that is responsible for decomposing the input grid into a more abstract representation.
This way we are trying to answer the question "which reversible function can produce the input grid and what would be its parameters?", but during the actual execution of the program, we will only run it backwards.

So the whole setup for program search would look like this:

- We have two trees of search trees, one for input grid and one for output grid.
- Each node in the main trees corresponds to a variable; they are connected by program blocks that perform transformations between them.
- Each node in any of the inner trees represents an unfinished program block that should generate a corresponding variable value when finished.
- The input grid search tree can only use reversible functions.
- When a program block is finished and is reversible, it is run backwards to validate it and generate new values for the variables that it uses. If successful, new variables are created in the main tree and get a new inner tree each.
- When a program block is finished and is not reversible, placeholder variables are created that hold only type information in the main tree, and no inner tree is created for them.
- Each time a new variable is created, the pattern matching algorithm tries to connect it with the variables in the other tree that have the same type. If after that a program block in the output tree has all its inputs connected to explained variables, it is run forward to check its validity, and its output variable gets the explained mark on success.
- When the output variable is explained, it means that there is a path from the input that covers all parts of its abstract representation, and the solution is found.

### Variables with multiple options or wildcards

If we start looking deeper into which functions are reversible and which are not, we can notice that for some functions we can't pin down one specific set of input values but can narrow it down to a set of limited possible options.
For example, when we try to run the function `concat` that concatenates two lists backwards, we can see that any split of the output list into two parts can be a valid pair of input values.
This is still very useful because it allows us to trim invalid search branches early, not much worse than if we had a single predicted set of input values.

There are two difficulties we get by introducing these variables:

First, we need to be able to represent variables with multiple options in the system.
One option would be to create a separate tree for each option, but if we factor in the fact that options for each example are independent, the number of all possible combinations quickly becomes way too large.
Alternatively, we can create a special data structure that would represent a set of possible values for a variable and has a way to pair up corresponding option values in other variables.
This is more space and computationally efficient but requires implementing some additional logic to handle it.
We need to learn how to build and run in reverse new program blocks that have a multi-option variable as their desired output, our pattern matching algorithm that connects known and unknown variables needs to be able to handle it, and when this matching happens, we need to select the chosen option for all other connected variables.

Second, if we are looking for better input representations, we can't keep this superposition of possible values for a variable because there is no other data that can help us decide which one is the correct or more useful one.
To deal with this, we add a special function `fix_rev_param` that wraps a reversible subexpression and forces one of its parameters to be a specific value that is generated by another parameter function.
For example, if we have an expression `(rev_select_grid (lambda (eq? $0 $v1)) $v2 $v3)` that splits grid cells of one color from the others when run in reverse, the chosen color value goes into variable `$v1`, cells of that color go into `$v2`, and the rest of the cells go into `$v3`.
If we have a mix of black and blue cells, we can see them both as blue cells on a black background, or as black cells on a blue background, and for an input representation, we have to choose one of these interpretations.
The easiest way would be to decide "Ok, the background is black", and we can represent this as `(rev_fix_param (rev_select_grid (lambda (eq? $0 $v1)) $v2 $v3) $v1 (lambda Const(color, 0)))`.
Alternatively, we may want to perform some custom computation to compute the correct value, and it will go in the last lambda parameter, which receives the original grid as a parameter.

The next idea is about having wildcard items in data representations.
For example, if we want to split a grid into a background and a foreground, we may want to think of them as two grids that are drawn one on top of another.
To do this we need a way to represent an empty cell in the foreground grid, which means that it won't override the value of the background cell, and a way to represent a cell in the background grid that is under the cell in the foreground grid, so it can actually be of any color.
We do this by using `nothing` as an empty value, and `any_object` as a wildcard value, plus we wrap the whole variable value with `PatternWrapper` structure that helps us distinguish between variables that have wildcards and variables that don't, which helps us speed up the pattern matching process.

Finally, for some functions, we can't predict their inputs just from the output alone, but if we know the output and one of the inputs, we can predict the second input.
For example, function `+` can have an infinite number of input pairs that would produce the same given output, but if we know one of the inputs, the second one can be easily calculated.
We are calling these variables abductible because the procedure of determining the second input parameter once we have a premise about the first one is akin to logical abduction.

### Guiding system

How can we steer the search process towards finding solutions not only by pruning completely hopeless branches but also by exploring the most promising ones earlier?

In DreamCoder, it's fairly simple.
We are running Dijkstra's algorithm on the infinite tree of all possible partial programs starting from an empty one. Each edge corresponds to a function that fills the first hole in the program and has a weight that corresponds to the negative log likelihood of the function being the correct choice towards the solution.
These weights are approximated by a neural network that takes input and output values for task examples and returns a single set of weights that would be used for the whole search process, which has limited precision for more complex tasks and larger programs.

But our search space is more complex; we have two trees of search trees, which introduces both difficulties and opportunities.

First, we can have a different set of weights for each search subtree, specific to the variable value that serves as the root of this subtree.
This can make them more precise because different functions can be useful to process different values in different parts of the program, and we won't have to rely on some average that would be somewhat useful everywhere.

#### Neural network architecture

In order to support variable-specific weights and to avoid rebuilding and retraining the whole network after adding each new function to the grammar, we use a custom neural network architecture, inspired by [Pointer Networks](https://arxiv.org/abs/1506.03134) and [CLIP](https://arxiv.org/abs/2103.00020).

It consists of several parts:

- Domain-specific encoder that takes input and output values for task examples and encodes them into a fixed-size vector. For ARC, we are using a CNN-based network with slight modifications to support grids of different sizes.
- Encoder for intermediate variable values. It should support values of every possible type that can be used in the program, so we serialize them into strings and use an off-the-shelf embedding transformer model to encode them.
- Encoder for the current grammar. We are using the same embedding model to get an embedding vector for each function in the grammar, and then use their average as an embedding vector for the whole grammar.
- State processor that takes embeddings for task inputs, outputs, intermediate variable values, and the full grammar, plus a flag that indicates if the program is reversed, and produces a single vector that serves as a state of the current program. It is implemented as a dense neural network.
- And finally, a decoder that takes the state vector and embeddings for each function in the grammar, combines them into a 2D-batch where one batch dimension corresponds to the functions, and the other corresponds to the state vectors, and produces a matrix of weights for each function. It is implemented as a dense neural network with a softmax activation function in the end.

To improve performance, embeddings for intermediate variable values and functions are cached in Redis or SQLite database since we are not changing the weights of the transformer model.
Encodings for task examples are cached in memory for inference and reset for each training cycle.

As for the training data, we are using the solutions found by the system in previous iterations.
Each program block in the solution program corresponds to one datapoint, so one solution can provide us with a couple of dozen datapoints and not just one, as in DreamCoder.
This makes our inability to "dream up" new programs and tasks less of an issue.
To get all the data we need at training time, we are storing not only the solution programs but also the values of all intermediate variables that were used in them.

We use the same loss function as in DreamCoder, where the generated weights are log likelihoods of the functions being used in the solution programs, with the goal that for every point where a function was chosen in the search process, it would have the highest weight among the other functions that could have been chosen in this place.

#### Adding manually written solutions to the training data

Writing new reversible functions can be quite complicated, and we want the system to be as flexible as possible in using all the primitive functions, so we prefer to keep the starting library of functions as small as possible.
This means that meaningful programs can get really complex very quickly, and it makes it less probable that the system will find the useful abstractions for them in a reasonable amount of time.

We've decided that the suitable middle ground would be to manually write some solutions for tasks with important concepts and let the system extract composite functions from them and train the neural network on their traces.

Since lambda calculus is not the most pleasant language to write programs in, we also have a [script](https://github.com/andreyz4k/expcoder/blob/main/src/solution_builder.jl) that helps with that by running partially written programs, showing the gaps, and trying to fill them as the usual solver process.

#### Using representation complexity

The neural guiding system helps us to have a search priority in each of the inner search trees, but how do we choose which search tree to explore on each iteration?

One option would be to use one big priority queue for all the branches in all the search trees or two trees, one for input and one for output, but this prevents us from having a heuristic that uses variable values themselves.

As humans, we are very averse to handling complex objects with all their details in our minds, and it may help us to quickly narrow down towards the most structured and neat representation possible.
We can use the same idea in our system.

One way to define data complexity is to use the notion of Kolmogorov complexity, which is the length of the shortest program that can generate the data.
But we don't know this program and our goal is to find it, or something like it, so we have to use some other definition which can be used for any data structure without performing a lot of computations.

We chose to use a weighted sum of the counts of items of each type in the data structure.
For example, if we have a list with 5 tuples of 2 integers each, we will count 1 for the list, 5 for tuples, and 10 for integers.
Weights for each type are hyperparameters.

Ok, we know the complexity of a single variable; does it mean that any variable storing a single integer will get the highest priority?

Not exactly.
When we add a reversible program block that has several input variables, they all are parts of the data representation for the original variable, so we consider them connected.
This way, the complexity factor for any variable is the sum of its own complexity and the complexity of all its connected variables.

But what if the first transformation was not that great in reducing data complexity but the further one was?
For example, if we separate a grid into a background and a foreground grid, complexity only rises because now we have two grids instead of one.
But then we see that the background grid can be generated by the function `repeat_grid` that takes only `item`, `height`, and `width` as parameters, which sum up to a very low complexity.
Now we want to push the foreground grid higher in the priority queue because we found a simpler representation for its connected variable.
We do it by declaring that the complexity factor of the variable is the sum of its own complexity and the complexity of the simplest representation of its connected variables.

Let's bring it all together.
Each variable has a path from it to the root of the search tree; that path has some cost.
Then it has its own search tree with a number of prototype programs to explore, each of them has a cost.
Additionally, it has a complexity factor that can be changed when we find a new representation for one of its connected variables.
The final priority value for each prototype program is computed using these three values; the exact parameters can be defined as hyperparameters.

The tricky part here is that we want to update priorities for all the prototypes in the variable's search tree when we update its complexity factor.
Iterating over all of them would be too expensive, so we separate the priority queue into two levels.
Each variable has its own priority queue for program prototypes that uses only their cost as a priority.
And then we have a priority queue for variables that uses the cost of the best prototype in the variable's search tree, the complexity factor, and the cost of the path from the variable to the root of the search tree.
So when we update the complexity factor for a variable, we can just update the priority of the variable in the top-level priority queue.

The final point is that we use [Non-deterministic priority queues](https://github.com/andreyz4k/NDPriorityQueues.jl) for the top-level queues in order to prevent the search process from getting stuck in a local minimum.

### Learning new functions

We are using a [slightly modified version](https://github.com/andreyz4k/stitch) of the [STITCH](https://arxiv.org/abs/2211.16605) algorithm for learning new useful functions.
It searches for repeating patterns in the solutions found by the system, saves them as new composite functions, and rewrites the solution programs using them.

## Example solutions

#### [c9e6f938.json](https://arcprize.org/play?task=c9e6f938)

This simple task requires mirroring the original input grid vertically and adding it to the original grid to the right.

```lisp
let $v1 = rev($inp0 = (columns_to_grid $v1)) in
let $v2 = rev($v1 = (reverse $v2)) in
let $v3 = (concat $v1 $v2) in
(columns_to_grid $v3)
```

#### [4c7a5b59.json](https://github.com/andreyz4k/expcoder/blob/main/data/sortOfARC/4c7a5b59.json)

This task from the [SortOfARC](https://openreview.net/pdf?id=rCzfIruU5x5) dataset requires replacing all pink objects with an object of a specific fixed shape.

```lisp
let $v1, $v2, $v3 = rev($inp0 = (rev_fix_param (rev_select_grid (lambda (eq? $0 $v1)) $v2 $v3) $v1 (lambda Const(color, 0)))) in
let $v4, $v5, $v6 = rev($v2 = (repeat_grid $v4 $v5 $v6)) in
let $v7 = (repeat_grid $v4 $v5 $v6) in
let $v8, $v9, $v10 = rev($v3 = (rev_grid_elements $v8 $v9 $v10)) in
let $v11 = rev($v8 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (and (not (gt? (abs (- (tuple2_second (tuple2_first $0)) (tuple2_second (tuple2_first $2)))) 1)) (not (gt? (abs (- (tuple2_first (tuple2_first $0)) (tuple2_first (tuple2_first $2)))) 1)))) $0))) $1 $0))) empty_set $v11)) in
let $v12 = rev($v11 = (map_set (lambda (map_set (lambda (tuple2 $0 (tuple2_second $1))) (tuple2_first $0))) $v12)) in
let $v13, $v14, $v15 = rev($v12 = (rev_fix_param (rev_select_set (lambda (eq? (tuple2_second $0) $v13)) $v14 $v15) $v13 (lambda Const(color, 6)))) in
let $v16 = rev($v14 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first $0) (tuple2_first $1)) (+ (tuple2_second $0) (tuple2_second $1)))) $1) $0 (lambda (tuple2 (fold (lambda (lambda (if (gt? $0 $1) $1 $0))) (map (lambda (tuple2_first $0)) (collect $0)) max_int) (fold (lambda (lambda (if (gt? $0 $1) $1 $0))) (map (lambda (tuple2_second $0)) (collect $0)) max_int))))) (tuple2_first (tuple2_first $1)))) (tuple2_second (tuple2_first $0))) (tuple2_second $0))) $v16)) in
let $v17, $v18 = rev($v16 = (map_set (lambda (tuple2 $0 $v17)) $v18)) in
let $v19 = Const(set(tuple2(int, int)), Set([(0, 0), (1, 2), (0, 2), (1, 1), (0, 1), (2, 2), (2, 1), (1, 0)])) in
let $v20 = (map_set (lambda (tuple2_first $0)) $v18) in
let $v21 = (map_set (lambda (tuple2 $0 $v19)) $v20) in
let $v22 = (map_set (lambda (tuple2 $0 $v17)) $v21) in
let $v23 = (map_set (lambda (tuple2 ((lambda ((lambda (rev_fix_param (map_set (lambda (tuple2 (+ (tuple2_first $0) (tuple2_first $1)) (+ (tuple2_second $0) (tuple2_second $1)))) $1) $0 (lambda (tuple2 (fold (lambda (lambda (if (gt? $0 $1) $1 $0))) (map (lambda (tuple2_first $0)) (collect $0)) max_int) (fold (lambda (lambda (if (gt? $0 $1) $1 $0))) (map (lambda (tuple2_second $0)) (collect $0)) max_int))))) (tuple2_first (tuple2_first $1)))) (tuple2_second (tuple2_first $0))) (tuple2_second $0))) $v22) in
let $v24 = (rev_select_set (lambda (eq? (tuple2_second $0) $v13)) $v23 $v15) in
let $v25 = (map_set (lambda (map_set (lambda (tuple2 $0 (tuple2_second $1))) (tuple2_first $0))) $v24) in
let $v26 = (rev_fold_set (lambda (lambda (rev_greedy_cluster (lambda (lambda (any_set (lambda (not (gt? (+ (abs (- (tuple2_first (tuple2_first $0)) (tuple2_first (tuple2_first $2)))) (abs (- (tuple2_second (tuple2_first $0)) (tuple2_second (tuple2_first $2))))) 1))) $0))) $1 $0))) empty_set $v25) in
let $v27 = (rev_grid_elements $v26 $v9 $v10) in
(rev_select_grid (lambda (eq? $0 $v1)) $v7 $v27)
```
As you can see, even solutions for fairly simple tasks can be hard to read; this is the cost of having a simple language with few primitive functions.

## Limitations

As a curriculum learning system, ExpCoder relies heavily on the gradual increase in complexity of tasks it tries to solve.
If there is a large gap between the tasks it has already solved and the rest, the chances of it bridging that gap in a reasonable amount of time are not great.

Another limitation is that every reversible program block is expected to be self-contained, which means that it cannot use information from variables in other branches of the search tree.
In some tasks, this can be an issue when there is a natural way to split data into separate variables, but further processing of one of them still requires information from the other one.

ExpCoder is better suited for tasks that require understanding what is going on, finding abstract representations, and connecting them together, rather than for tasks that require performing a sequence of transformations on the data.
It is much harder to represent these kinds of algorithms in lambda calculus, as it would require putting the logic into the `fold` function, which is possible but does not allow any introspection of intermediate data representations.

## How to run

After cloning the repository, you can launch julia REPL with the following command:

```bash
julia --project=.
```

Then you'll need to install the dependencies:

```julia
]instantiate
```

And then you can run the system:

```julia
using solver
solver.main(iterations=12, model="standalone", workers=8, timeout=20)
```

This will run the system for 12 solve-compress-train cycles, using 8 solver workers and 20 seconds for solving each task.
The standalone model means that it will use the neural guiding model that runs in a separate Python process, using CUDA or MPS if available.
It is advised to set the worker count to the number of available CPU cores minus 1-2 for the main and guiding processes.

## Acknowledgments

Part of this work was supported by a grant from [Noeon.ai](https://noeon.ai).
