# Rholang cost stacks with a shared prefix

The cost surface form `{% P %}[s]` signs process `P` with one cost signature
`s`. Separately, `s :: S` offers a stack of authority. A stack can continue
linearly or fork after that prefix,
`s :: (A | B)`. The fork is **not** two copies of `s`: every prefix cell is
transferred and consumed once. Both children become eligible only after the
prefix was completely consumed in an earlier event; afterwards they advance
independently. Nested forks apply the same rule at every ancestor.

For example, `a :: (b :: () | c :: ())` has three transfer cells in
preorder (`a`, `b`, `c`), but only one physical `a` cell. A draw for `b`
or `c` before the `a` event, or in that same event, is invalid. After
`a`, either sibling may be drawn first; drawing one does not advance the
other.

The MeTTaIL `language!` grammar represents a fork as `CostStackPar`; the
Rholang lowering worklist constructs one `CostStack` with ordered `cells` and
`parallel_tail` children. No second parser, string reparse, or implicit
duplicated stack is involved. The preorder flattening of its cells exists only
to keep transfer-event identities compatible with the linear protocol. The
tree remains the sole source of branch gates.

For root identity $`r`$ and authored path $`i_1,\ldots,i_n`$,
the branch identity is a domain-separated hash fold
$`\operatorname{child}(p,i)=H(\texttt{f1r3node:cost-accounted-rho:stack-branch:v1}\parallel p\parallel\operatorname{LE64}(i))`$.
The empty path is exactly $`r`$.
A branch carries its parent's ID and the length of that parent's remaining
prefix. A draw in event $`e`$ is ready only if every ancestor has already
reached that length **before** $`e`$; a prefix pop in the same event cannot
release a child. Sorting draw IDs cannot change that rule.

The physical inventory stores the historical linear root prefix in `stacks`
and, only for branched roots, one authenticated `stack_trees` sidecar.
Branch IDs, gates, transfer offsets, and current cells are derived by the
iterative `stack_branches` walker. `validate_stack_birth` compares a
claimed flat transfer-event list to the tree preorder without cloning either.
The walker and validator take no host-work budget. Their worklist and result
grow only with the branches and cells of the stack tree, and each growth uses
fallible allocation. A mismatched flat list, unknown branch, premature child draw,
or attempt to spend one cell twice is refused.

Settlement application follows the same boundary. It precharges the lane
walk and a depth-first lookup for every synthetic branch pop before changing
the inventory. A lookup reserves one candidate unit per entered branch, one
hash/preimage/digest charge per traversed child edge, and frame/path storage
before each worklist growth. The checked authored-index paths then let the
commit phase drain cells without another search or allocation. Thus a budget
refusal leaves the inventory unchanged. For a complete tree with $`N`$ branch
nodes, the lookup has $`N-1`$ child edges; an early match uses only a prefix
of those charges. A tree-free linear stack takes the historical application
path and incurs zero new branch-search charges. These count/prefix laws are
also proved in the formal model.

The protobuf `CostStack.parallel_tail` field is additive, tag 2. Legacy
event/cold-store bincode omits that field entirely, including its empty
length, so old linear bytes and hashes remain exact. CostV1 encodes and
decodes the tree. Linear authority witness IDs retain the v9 domain and
serialization; witnesses with any tree use a separate tree-bound domain.
This stack rule alone does not make an arbitrary Cost(G) grade fundable:
a selected, installed host projection must first reconstruct this exact
constructor profile and pass the separate live-supply admission check.

The one-prefix cursor and independent-sibling laws are proved in
[`RholangCostSurface.v`](../../formal/rocq/rho_bridge/theories/RholangCostSurface.v).
Executable obligations cover syntax and lowering
([`rholang_cost_syntax.rs`](../../languages/tests/rholang_cost_syntax.rs),
[`rholang_cost_lowering.rs`](../../rholang-runtime/tests/rholang_cost_lowering.rs)),
and the integration workspace covers legacy/CostV1 wire fixtures, deep
protobuf/trait teardown, and physical settlement.
