import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """

        #printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Check the data type before removing it from a list
        if isinstance(fact_or_rule, Fact) and (fact_or_rule in self.facts):
            kb_fact = self._get_fact(fact_or_rule)
            kb_fact.asserted = False
            if not kb_fact.supported_by:
                self.remove_helper(kb_fact)
            #Remove the fr from the actual KnowledgeBase
            if isinstance(kb_fact, Fact):
                self.facts.remove(kb_fact)
            else:
                self.rules.remove(kb_fact)

    def remove_helper(self, fr):
        #Check to see if fact or rule is asserted and not supported by anything
        if (not fr.asserted) and (not fr.supported_by):
            for dependencies in fr.supports_facts:
                dependencies.supported_by.remove(fr)
                self.remove_helper(dependencies)

            for dependencies in fr.supports_rules:
                dependencies.supported_by.remove(fr)
                self.remove_helper(dependencies)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        #create new binding by matching first left hand rule and fact
        new_binding = match(fact.statement, rule.lhs[0])

        if new_binding:
             if len(rule.lhs) > 1:
                 lhs_list = []
                 for statement in rule.lhs[1:]:
                     lhs_list.append(instantiate(statement, new_binding))

                 #make a rule by combining the new lhs and given rhs
                 new_rule = instantiate(rule.rhs, new_binding)
                 inferred_r = Rule([lhs_list, new_rule])

                 #rule and fact have inferred rule as dependent
                 rule.supports_rules.append(inferred_r)
                 fact.supports_rules.append(inferred_r)

                 #inferred rule is supported by provided rule and fact
                 inferred_r.supported_by.append([[fact, rule]])

                 #add inferred rule to KnowledgeBase
                 kb.kb_add(inferred_r)
             else:
                 #derive fact by matching first lhs with provided fact
                 new_fact = instantiate(rule.rhs, new_binding)
                 inferred_f = Fact(new_fact)

                 #rule and fact have inferred fact as dependent
                 fact.supports_facts.append(inferred_f)
                 rule.supports_facts.append(inferred_f)

                 ##inferred fact is supported by provided rule and fact
                 inferred_f.supported_by.append([[fact,rule]])

                 #add inferred fact to kb
                 kb.kb_add(inferred_f)
