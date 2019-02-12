# realloc-adv

Optimised version of the realloc backend - this version is more efficient and has a wider range of capabilities than the Hungarian algorithm-based version. Has the capability to process CSV inputs of availability.

## Usage

`python3 realloc.py input output [--cmds commands] [--multi count]`

Where
* `input` is a CSV file of tutor availabilities
* `output` is the CSV file or directory where the outputted allocation(s) will be stored
* `commands` is a txt file of optional commands
* `count` is the number of outputs to generate (if `count` > 1, `output` should be a directory)

## Requirements

Python version 3.4 or higher and the Z3 command line tool are required to run realloc.

## Input and Output Format

Input should be formatted as a table with tutors as columns and classes as rows. Each tutor/class intersection should contain the character 'A' (denoting available) or 'U' (denoting unavailable). An example can be seen below:

```
,Alice,Bob,Charlie
T01,A,A,U
T02,U,A,U
T03,A,U,A
```
(or in visual form:)

|     | Alice | Bob | Charlie |
|-----|-------|-----|---------|
| T01 | A     | A   | U       |
| T02 | U     | A   | U       |
| T03 | A     | U   | A       |

Output will be similarly formatted, with 'Y' denoting an allocated slot, and 'N' denoting an unallocated slot. An example allocation can be seen below, allocating Alice to T01, Bob to T02, and Charlie to T03:

```
,Alice,Bob,Charlie
T01,Y,N,N
T02,N,Y,N
T03,N,N,Y
```
(or in visual form:)

|     | Alice | Bob | Charlie |
|-----|-------|-----|---------|
| T01 | Y     | N   | N       |
| T02 | N     | Y   | N       |
| T03 | N     | N   | Y       |

## Commands

A specialised command language has been designed for specifying extra properties for the allocation. Any commands should be placed on separate lines of a txt file, and passed into the allocator using the `--cmds` option.

The format for specifying commands is as follows:

`(C | T) (regex pattern to match) => (method to execute) {params}`

The `C` option is used to run the command on classes, while the `T` option is used to run the command on tutors. Example usage for each method is described below:

### Tutor count

Set the number of tutors on each class to 1:

```
C .* => set_exact_tutor_limit 1
```

Set the number of tutors on each prac to be between 2 and 4 (inclusive):

```
C P.* => set_lower_tutor_limit 2
C P.* => set_upper_tutor_limit 4
```

### Tutorial length

Set the duration of each tutoral to be 2 hours (if no duration is set, all classes are 1 hour long):

```
C T.* => set_duration 2
```

### Clashes

Set a clash between T01 and T02:

```
C T01 => set_clash T02
```

Prevent tutor Bob from doing both T01 and T02:

```
C T01 => set_single_clash T02 Bob
```

NOTE: Clashes are commutative, that is, if you set a clash between T01 and T02, you do not have to set a separate clash between T02 and T01

### Min/max hours

Set the minimum number of hours per week for all tutors to 3:

```
T .* => set_lower_class_limit 3
```

Set the maximum number of hours per week for tutor Bob to 10:

```
T Bob => set_upper_class_limit 10
```

Set the minimum number of practical hours per week for all tutors to 2:

```
T .* => set_lower_type_limit P.* 2
```

Set the maximum number of tutorial hours per week for tutor Bob to 3:

```
T Bob => set_upper_type_limit T.* 3
```

### Junior/Senior tutor pairing

Set Alice as a senior tutor and Bob as a junior tutor (the allocator will attempt to pair all junior tutors with a senior tutor)

```
T Alice => set_senior
T Bob => set_junior
```

NOTE: if using this option, make sure there is room for both a junior and senior tutor on each class - if you do not want junior/senior pairing on a class you can use the no_pair command, as seen below:

```
C T01 => no_pair
```

(aside: for more accurate regex matching of three-character class codes, a regex pattern such as `^P\d\d$` (for matching all practicals in this case) should be used)
