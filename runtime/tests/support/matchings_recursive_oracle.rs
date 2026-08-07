use std::collections::HashSet;

pub(crate) fn enumerate<T: Clone>(candidates: &[Vec<(usize, T)>]) -> Vec<(Vec<T>, HashSet<usize>)> {
    fn visit<T: Clone>(
        candidates: &[Vec<(usize, T)>],
        group: usize,
        chosen: &mut Vec<(usize, T)>,
        used: &mut HashSet<usize>,
        out: &mut Vec<(Vec<T>, HashSet<usize>)>,
    ) {
        if group == candidates.len() {
            out.push((
                chosen.iter().map(|(_, payload)| payload.clone()).collect(),
                chosen.iter().map(|(index, _)| *index).collect(),
            ));
            return;
        }
        for (index, payload) in &candidates[group] {
            if used.contains(index) {
                continue;
            }
            used.insert(*index);
            chosen.push((*index, payload.clone()));
            visit(candidates, group + 1, chosen, used, out);
            chosen.pop();
            used.remove(index);
        }
    }

    let mut out = Vec::new();
    visit(candidates, 0, &mut Vec::new(), &mut HashSet::new(), &mut out);
    out
}
