use super::{try_reverse_task_batch, BindingFailure};
use std::cell::Cell;
use std::rc::Rc;

#[test]
fn exact_trace_and_every_refusal_preserve_the_paid_swap_prefix() {
    for length in 0..18 {
        for start in 0..=length {
            let original: Vec<_> = (0..length).collect();
            let swaps = (length - start) / 2;
            let mut expected_trace = vec![(3, 8)];
            for _ in 0..swaps {
                expected_trace.extend([(1, 0), (6, 4)]);
            }
            expected_trace.push((1, 0));
            let mut actual = original.clone();
            let mut trace = Vec::new();
            try_reverse_task_batch(&mut actual, start, &mut |w, u| {
                trace.push((w, u));
                Ok::<_, usize>(())
            })
            .expect("complete batch");
            let mut expected = original.clone();
            expected[start..].reverse();
            assert_eq!(actual, expected);
            assert_eq!(trace, expected_trace);
            assert_eq!(trace.iter().map(|(w, _)| w).sum::<usize>(), 4 + 7 * swaps);
            assert_eq!(trace.iter().map(|(_, u)| u).sum::<usize>(), 8 + 4 * swaps);

            for stop in 0..trace.len() {
                let mut actual = original.clone();
                let mut attempted = Vec::new();
                let result = try_reverse_task_batch(&mut actual, start, &mut |w, u| {
                    attempted.push((w, u));
                    if attempted.len() == stop + 1 {
                        Err(stop)
                    } else {
                        Ok(())
                    }
                });
                assert_eq!(result, Err(BindingFailure::Reservation(stop)));
                assert_eq!(attempted, trace[..=stop]);
                let completed_swaps = stop.saturating_sub(1) / 2;
                let mut expected = original.clone();
                for index in 0..completed_swaps {
                    expected.swap(start + index, length - 1 - index);
                }
                assert_eq!(actual, expected);
                assert_eq!(&actual[..start], &original[..start]);
            }
        }
    }
}

#[test]
fn invalid_start_keeps_diagnostic_and_reservation_precedence() {
    for start in [4, usize::MAX] {
        let mut values = [0, 1, 2];
        let mut trace = Vec::new();
        assert_eq!(
            try_reverse_task_batch(&mut values, start, &mut |w, u| {
                trace.push((w, u));
                Ok::<_, usize>(())
            }),
            Err(BindingFailure::InvalidCollectionInput(
                "binding task batch starts beyond the worklist"
            ))
        );
        assert_eq!(trace, [(3, 8), (1, 0)]);
        assert_eq!(values, [0, 1, 2]);
        for stop in 0..2 {
            let mut calls = 0;
            assert_eq!(
                try_reverse_task_batch(&mut values, start, &mut |_, _| {
                    let current = calls;
                    calls += 1;
                    if current == stop {
                        Err(stop)
                    } else {
                        Ok(())
                    }
                }),
                Err(BindingFailure::Reservation(stop))
            );
            assert_eq!(calls, stop + 1);
            assert_eq!(values, [0, 1, 2]);
        }
    }
}

#[test]
fn moved_tasks_need_no_clone_and_are_not_dropped_by_reversal() {
    struct Task {
        id: usize,
        drops: Rc<Cell<usize>>,
    }
    impl Drop for Task {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
        }
    }
    let drops = Rc::new(Cell::new(0));
    let mut tasks: Vec<_> = (0..5).map(|id| Task { id, drops: drops.clone() }).collect();
    try_reverse_task_batch(&mut tasks, 1, &mut |_, _| Ok::<_, ()>(()))
        .expect("move-only task reversal");
    assert_eq!(tasks.iter().map(|task| task.id).collect::<Vec<_>>(), [0, 4, 3, 2, 1]);
    assert_eq!(drops.get(), 0);
    drop(tasks);
    assert_eq!(drops.get(), 5);
}
