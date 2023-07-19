package io.microraft.impl;

import io.microraft.impl.local.LocalRaftGroup;
import io.microraft.test.util.BaseTest;
import org.junit.After;
import org.junit.Test;

import static io.microraft.RaftRole.FOLLOWER;
import static org.assertj.core.api.Assertions.assertThat;

public class VotePhaseValidationTest extends BaseTest {

    private LocalRaftGroup group;

    @After
    public void destroy() {
        if (group != null) {
            group.destroy();
        }
    }

    @Test
    public void testO() {
        group = LocalRaftGroup.start(3);
        RaftNodeImpl leader = group.waitUntilLeaderElected();

        // Repeat
        for (int i = 0; i < 3; i++) {
            System.out.printf("Pass %s.\n", i);
            RaftNodeImpl follower = group.getAnyNodeExcept(leader.getLocalEndpoint());
            leader.transferLeadership(follower.getLocalEndpoint()).join();
            leader = group.waitUntilLeaderElected();
        }

        // int term2 = getTerm(newLeader);
        // assertThat(newLeader).isNotSameAs(leader);
        // assertThat(term2).isGreaterThan(term1);
        // assertThat(getRole(leader)).isEqualTo(FOLLOWER);
    }
}
