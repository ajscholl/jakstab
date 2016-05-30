package org.jakstab.analysis.newIntervals.statistic;

import org.jakstab.util.Logger;

/**
 * Utility class to record statistic information for intervals.
 *
 * @author A. J. Scholl
 */
public class Statistic {

	private static final Logger logger = Logger.getLogger(Statistic.class);

	private static boolean hasNoStatistic = true;

	private static long bitNumberReuseCount = 0L;
	private static long bitNumberUseCount = 0L;
	private static long bitNumberCreateCount = 0L;

	private static long intervalElementReuseCount = 0L;
	private static long intervalElementUseCount = 0L;
	private static long intervalElementCreateCount = 0L;

	private static long ccIntervalElementReuseCount = 0L;
	private static long ccIntervalElementUseCount = 0L;
	private static long ccIntervalElementCreateCount = 0L;

	static {
		// register a hook to print the generated statistic.
		Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
			@Override
			public void run() {
				printStatistic();
			}
		}));
	}

	public static void activateStatistic() {
		hasNoStatistic = false;
	}

	/**
	 * Count the number of times a BitNumber could be reused.
	 */
	public static void countBitNumberReuse() {
		bitNumberReuseCount++;
	}

	/**
	 * Count the number of instances of bit numbers requested.
	 */
	public static void countBitNumberUse() {
		bitNumberUseCount++;
	}

	/**
	 * Count the number of instances of bit numbers created.
	 */
	public static void countBitNumberCreate() {
		bitNumberCreateCount++;
	}

	/**
	 * Count the number of times an IntervalElement could be reused.
	 */
	public static void countIntervalElementReuse() {
		intervalElementReuseCount++;
	}

	/**
	 * Count the number of instances of interval elements requested.
	 */
	public static void countIntervalElementUse() {
		intervalElementUseCount++;
	}

	/**
	 * Count the number of instances of interval elements created.
	 */
	public static void countIntervalElementCreate() {
		intervalElementCreateCount++;
	}

	/**
	 * Count the number of times an CongruenceClassInterval could be reused.
	 */
	public static void countCCIntervalElementReuse() {
		ccIntervalElementReuseCount++;
	}

	/**
	 * Count the number of instances of cc-interval elements requested.
	 */
	public static void countCCIntervalElementUse() {
		ccIntervalElementUseCount++;
	}

	/**
	 * Count the number of instances of cc-interval elements created.
	 */
	public static void countCCIntervalElementCreate() {
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
