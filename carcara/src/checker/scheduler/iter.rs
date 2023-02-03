use crate::ast::ProofCommand;

pub struct ScheduleIter<'a> {
    proof_stack: Vec<&'a [ProofCommand]>,
    steps: &'a Vec<(usize, usize)>,
    step_id: usize,
}

impl<'a> ScheduleIter<'a> {
    pub fn new(proof_commands: &'a [ProofCommand], steps: &'a Vec<(usize, usize)>) -> Self {
        Self {
            proof_stack: vec![proof_commands],
            steps,
            step_id: 0,
        }
    }

    /// Returns the current nesting depth of the iterator, or more precisely, the nesting depth of
    /// the last command that was returned. This depth starts at zero, for commands in the root
    /// proof.
    pub fn depth(&self) -> usize {
        self.proof_stack.len() - 1
    }

    /// Returns `true` if the iterator is currently in a subproof, that is, if its depth is greater
    /// than zero.
    pub fn is_in_subproof(&self) -> bool {
        self.depth() > 0
    }

    /// Returns a slice to the commands of the inner-most open subproof.
    pub fn current_subproof(&self) -> Option<&[ProofCommand]> {
        self.is_in_subproof()
            .then(|| *self.proof_stack.last().unwrap())
    }

    /// Returns `true` if the last command that was returned was the end step of the current
    /// subproof.
    pub fn is_end_step(&self) -> bool {
        self.is_in_subproof()
            && self.steps[self.step_id - 1].1 == self.proof_stack.last().unwrap().len() - 1
    }

    /// Returns the command referenced by a premise index of the form (depth, index in subproof).
    /// This method may panic if the premise index does not refer to a valid command.
    pub fn get_premise(&self, (depth, index): (usize, usize)) -> &ProofCommand {
        &self.proof_stack[depth][index]
    }
}

impl<'a> Iterator for ScheduleIter<'a> {
    type Item = &'a ProofCommand;

    fn next(&mut self) -> Option<Self::Item> {
        // If it isn't the end of the steps
        if self.step_id < self.steps.len() {
            self.step_id += 1;
            let cur_step = self.steps[self.step_id - 1];
            // If current step is an closing subproof
            if let (_, usize::MAX) = cur_step {
                return Some(&ProofCommand::Closing);
            }
            while cur_step.0 != self.proof_stack.len() - 1 {
                self.proof_stack.pop();
            }

            let top = self.proof_stack.last().unwrap();
            let command = &top[cur_step.1];
            if let ProofCommand::Subproof(subproof) = command {
                self.proof_stack.push(&subproof.commands);
            }
            Some(command)
        } else {
            None
        }
    }
}
