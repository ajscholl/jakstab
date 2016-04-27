package org.jakstab.analysis.newIntervals.statistic;

import org.jakstab.util.Logger;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Statistic {

	private static final Logger logger = Logger.getLogger(Statistic.class);

	private static boolean hasNoStatistic = true;

	private static final MemoryWatcher watcher = new MemoryWatcher();
	private static final Thread watcherThread = new Thread(watcher);

	private static long bitNumberReuseCount = 0L;
	private static long bitNumberUseCount = 0L;
	private static long bitNumberCreateCount = 0L;

	private static long intervalElementReuseCount = 0L;
	private static long intervalElementUseCount = 0L;
	private static long intervalElementCreateCount = 0L;

	private static long ccIntervalElementReuseCount = 0L;
	private static long ccIntervalElementUseCount = 0L;
	private static long ccIntervalElementCreateCount = 0L;

	private static class MemoryWatcher implements Runnable {
		private final List<Long> usedMemory = new ArrayList<>();
		private boolean keepGoing = true;

		@Override
		public void run() {
			while (keepGoing) {
				try {
					Thread.sleep(10L);
					usedMemory.add(Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory());
				} catch (InterruptedException ignore) {
					keepGoing = false;
				}
			}
		}

		List<Long> getUsedMemory() {
			while (keepGoing) {
				try {
					Thread.sleep(10L);
				} catch (InterruptedException ignore) {
					// ignore exception
				}
			}
			return usedMemory;
		}
	}

	static {
		watcherThread.start();

		// register a hook to print the generated statistic.
		Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
			@Override
			public void run() {
				watcherThread.interrupt();
				List<Long> usedMemory = watcher.getUsedMemory();
				printMemoryStatistic(usedMemory);
				printStatistic();
			}
		}));
	}

	/**
	 * Print a summary of the used memory.
	 *
	 * @param usedMemory The used memory in bytes.
	 */
	private static void printMemoryStatistic(List<Long> usedMemory) {
		if (usedMemory.isEmpty()) {
			return;
		}
		long maxUsed = Collections.max(usedMemory);
		logger.info("Sampled " + usedMemory.size() + " times");
		logger.info("Maximum used memory: " + formatMem(maxUsed));
		for (long m : usedMemory) {
			logger.debug(formatMem(m));
		}
	}

	/**
	 * Format memory numbers. Does not work for negative numbers.
	 *
	 * @param m Memory in bytes.
	 * @return Memory in readable format.
	 */
	private static String formatMem(long m) {
		long b = m % 1024L;
		m /= 1024L;
		long kb = m % 1024L;
		m /= 1024L;
		long mb = m % 1024L;
		m /= 1024L;
		long gb = m % 1024L;
		m /= 1024L;
		long tb = m % 1024L;
		m /= 1024L;
		long pb = m;
		StringBuilder s = new StringBuilder();
		if (pb > 0L) {
			s.append(pb).append(" PB");
		}
		if (tb > 0L) {
			s.append(pb).append(" TB");
		}
		if (gb > 0L) {
			s.append(pb).append(" GB");
		}
		if (mb > 0L) {
			s.append(pb).append(" MB");
		}
		if (kb > 0L) {
			s.append(pb).append(" KB");
		}
		if (b > 0L) {
			s.append(pb).append(" B");
		}
		return s.toString();
	}

	/**
	 * Count the number of times a BitNumber could be reused.
	 */
	public static void countBitNumberReuse() {
		hasNoStatistic = false;
		bitNumberReuseCount++;
	}

	/**
	 * Count the number of instances of bit numbers requested.
	 */
	public static void countBitNumberUse() {
		hasNoStatistic = false;
		bitNumberUseCount++;
	}

	/**
	 * Count the number of instances of bit numbers created.
	 */
	public static void countBitNumberCreate() {
		hasNoStatistic = false;
		bitNumberCreateCount++;
	}

	/**
	 * Count the number of times an IntervalElement could be reused.
	 */
	public static void countIntervalElementReuse() {
		hasNoStatistic = false;
		intervalElementReuseCount++;
	}

	/**
	 * Count the number of instances of interval elements requested.
	 */
	public static void countIntervalElementUse() {
		hasNoStatistic = false;
		intervalElementUseCount++;
	}

	/**
	 * Count the number of instances of interval elements created.
	 */
	public static void countIntervalElementCreate() {
		hasNoStatistic = false;
		intervalElementCreateCount++;
	}

	/**
	 * Count the number of times an CongruenceClassInterval could be reused.
	 */
	public static void countCCIntervalElementReuse() {
		hasNoStatistic = false;
		ccIntervalElementReuseCount++;
	}

	/**
	 * Count the number of instances of cc-interval elements requested.
	 */
	public static void countCCIntervalElementUse() {
		hasNoStatistic = false;
		ccIntervalElementUseCount++;
	}

	/**
	 * Count the number of instances of cc-interval elements created.
	 */
	public static void countCCIntervalElementCreate() {
		hasNoStatistic = false;
		ccIntervalElementCreateCount++;
	}

	/**
	 * Output the generated statistic if one exists, otherwise do nothing.
	 */
	private static void printStatistic() {
		if (hasNoStatistic) {
			return;
		}

		logger.info("*** BitNumber ***");
		logger.info("Created: " + bitNumberCreateCount);
		logger.info("Requested: " + bitNumberUseCount);
		logger.info("Reused: " + bitNumberReuseCount);
		logger.info("");

		logger.info("*** Interval ***");
		logger.info("Created: " + intervalElementCreateCount);
		logger.info("Requested: " + intervalElementUseCount);
		logger.info("Reused: " + intervalElementReuseCount);
		logger.info("");

		logger.info("*** CCInterval ***");
		logger.info("Created: " + ccIntervalElementCreateCount);
		logger.info("Requested: " + ccIntervalElementUseCount);
		logger.info("Reused: " + ccIntervalElementReuseCount);
		logger.info("");
	}

}
