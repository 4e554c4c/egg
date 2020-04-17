# egg: egraphs good

This is a submission for Oliver Flatt and Calvin Lee's Software Verification final project at the U of U.


This folder contains the final branch of the implementation of E-Graph matching inspired by the RETE algorithm.

The main file to look at is src/rete.rs, which is used by src/egraph.rs.

Another file to look at is tests/timing.rs, which contains a file that times the performance of the algorithm with rewrite rules taken from the Herbie project.
Run these tests with the command `cargo test time_egg --release -- --nocapture --ignored`


Also note that not all the tests in lambda.rs pass (known bug), but the tests in math.rs pass. Verify this using `cargo test math`.

After learning about potential speedups from experimenting with RETE, the final product of the project is a PR to the `egg` project. This PR got merged into master, and can be seen here:
[https://github.com/mwillsey/egg/pull/21]
(https://github.com/mwillsey/egg/pull/21)
The PR has more details about the contents.