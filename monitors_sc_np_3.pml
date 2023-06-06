#define READERS 2
#define WRITERS 2
#define procId (_pid - 1)
#define NO_READ_NOTIFICATION -1
#define ALL 4
#define REAL_TRUE (1 == 1)

#define queueLength ((RW.queue.rear - RW.queue.front + ALL) % ALL + 1)

bool inStart[ALL];
bool inCS[ALL];

typedef queueT {
    int front = -1;
    int rear = -1;
    byte array[ALL];
}

typedef monitor {
    int readers = 0;
    int writers = 0;
    int blockedReaders = 0;

    bool blocked[ALL];

    queueT queue;

    byte lock = 0;
}

inline isQueueEmpty() {
    RW.queue.front == -1 && RW.queue.rear == -1;
}

inline enqueue() {
    if
    :: isQueueEmpty() ->{
        RW.queue.front = 0;
        RW.queue.rear = 0;
    }
    :: else -> {
        RW.queue.rear = (RW.queue.rear + 1) % ALL;
    }
    fi;
    RW.queue.array[RW.queue.rear] = procId;
    printf("MSC: enqueued\n");
}

inline dequeue() {
    if
    :: isQueueEmpty() ->{
        printf("MSC: error: no elems in queue\n");
    }
    :: else ->{
        if  
        :: (RW.queue.front == RW.queue.rear) ->{
            RW.queue.front = -1;
            RW.queue.rear = -1;
        };
        :: else -> RW.queue.front = (RW.queue.front + 1) % ALL;
        fi;
    }
    fi;
    printf("MSC: dequeued\n");
}

inline enterMon() {
    atomic {
        RW.lock == 0;
        RW.lock++;
    }
}


inline leaveMon() {
    atomic {
        RW.lock--;
    }
}


inline wait() {
    printf("MSC: now wait\n");
    RW.blocked[procId] = true;

    leaveMon();
    !RW.blocked[procId];
    enterMon();
}

inline notifyAll() {
    printf("MSC: notifyAll\n");
    k = 0;
    do
    :: k < ALL -> {
        atomic {
            RW.blocked[k] = false;
            k++;
        }
    }
    :: else -> break;
    od;
    k = 0;
}

inline startRead() {
    
    enterMon();

    printf("MSC: try read\n");

    r_start:
    enqueue();

    inStart[procId] = true;

    do
    :: (RW.writers != 0) -> {
        RW.blockedReaders++;
        wait();
        printf("MSC: unblocked\n");
        RW.blockedReaders--;
    }
    :: else -> {
        if
        :: RW.queue.array[RW.queue.front] == procId -> {
            break;
        }
        :: else -> {
            RW.blockedReaders++;
            wait();
            printf("MSC: unblocked\n");
            RW.blockedReaders--;
        }
        fi;
    };
    od;

    dequeue();

    if
    :: RW.blockedReaders > 0 -> {
        notifyAll();
    }
    :: else -> skip;
    fi;

    printf("MSC: blocked readers: %d\n", RW.blockedReaders);
    inStart[procId] = false;
    RW.readers++;
    printf("MSC: readers - %d\n", RW.readers);
    leaveMon();
}

inline endRead() {
    enterMon();

    inCS[procId] = false;

    RW.readers--;
    printf("MSC: readers - %d\n", RW.readers);
    notifyAll();

    leaveMon();
}

inline startWrite() {
    enterMon();

    printf("MSC: try write\n");
    
    w_start:
    enqueue();
    inStart[procId] = true;

    do
    :: (RW.writers != 0 || RW.readers != 0) -> {
        wait();
    }
    :: else -> {
        if
        :: RW.queue.array[RW.queue.front] == procId -> {
            break;
        }
        :: else -> {
            wait();
        }
        fi;
    }
    od;

    dequeue();
    inStart[procId] = false;
      
    RW.writers++;
    printf("MSC: writers - %d\n", RW.writers);

    leaveMon();
}

inline endWrite() {
    enterMon();

    inCS[procId] = false;

    RW.writers--;
    printf("MSC: writers - %d\n", RW.writers);
    notifyAll();

    leaveMon();
}

monitor RW;

proctype reader() {
    byte k = 0;
    do
    :: REAL_TRUE -> {
          printf("MSC: in non-cs\n");
    };
    :: true -> {
        k = 0;
        
        startRead();
        if
        :: RW.writers != 0 ->
            r_in_cs_when_w_already_in_cs: {skip;}
        :: else -> skip;
        fi;
        inCS[procId] = true;
        r_in_cs: printf("MSC: in cs\n");
        endRead();
    };
    od;
}

proctype writer() {
    byte k = 0;
    do
    :: REAL_TRUE -> {
        printf("MSC: in non-cs\n");
    }
    :: true -> {
        k = 0;
        
        startWrite();
        if
        :: RW.readers != 0 ->
            w_in_cs_when_r_already_in_cs: {skip;}
        :: RW.writers > 1 ->
            w_in_cs_when_w_already_in_cs: {skip;}
        :: else -> skip;
        fi;
        inCS[procId] = true;
        w_in_cs: printf("MSC: in cs\n");
        endWrite();
    };
    od;
}

init {
    atomic {
        int j = 0;
      
        do
        :: (j < READERS) -> {
            run reader();
            j++;
        }
        :: else -> break;
        od;
    
        j = 0;

        do
        :: (j < WRITERS) -> {
            run writer();
            j++;
        }
        :: else -> break;
        od;
    }
}
