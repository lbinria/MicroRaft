package io.microraft.impl;

import io.microraft.Ordered;
import io.microraft.impl.local.LocalRaftGroup;
import io.microraft.test.util.BaseTest;
import org.junit.After;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;

import static io.microraft.impl.local.SimpleStateMachine.applyValue;

public class AppendEntryValidationTest2 extends BaseTest {

    private LocalRaftGroup group;

    @After
    public void destroy() {
        if (group != null) {
            group.destroy();
        }
    }

    @Test
    public void appendEntries() {
        group = LocalRaftGroup.start(3);
        RaftNodeImpl leader = group.waitUntilLeaderElected();
        List<CompletableFuture<?>> t = new ArrayList<>();
        for (int n = 0; n < 10; n++) {
            for (int i = 1; i < 5; i++) {
                t.add(leader.replicate(applyValue("v_" + i)));
            }
        }
        CompletableFuture.allOf(t.toArray(CompletableFuture[]::new)).join();

        // CompletableFuture.allOf(leader.replicate(applyValue("v_1")),
        // leader.replicate(applyValue("v_2")),
        // leader.replicate(applyValue("v_3")), leader.replicate(applyValue("v_4")),
        // leader.replicate(applyValue("v_5"))).join();

        for (int i = 0; i < 2; i++) {
            RaftNodeImpl follower = group.getAnyNodeExcept(leader.getLocalEndpoint());
            leader.transferLeadership(follower.getLocalEndpoint()).join();
            leader = group.waitUntilLeaderElected();
            leader.replicate(applyValue("v_6")).join();
        }
    }

}
