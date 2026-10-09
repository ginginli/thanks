/**
 * HostCalc Pro — Thanksgiving planning engine (pure logic, no DOM).
 *
 * Works both in the browser (window.ThanksgivingPlanner) and in Node
 * (module.exports) so the math can be unit-tested independently.
 *
 * Model assumptions (aligned with omnicalculator.com/food/thanksgiving):
 *  - Children (under 12) eat roughly half an adult portion.
 *  - Whole turkey: 1.5 lbs per equivalent adult.
 *  - Leftovers: "light" buffers the turkey, potatoes and dinner rolls by
 *    +30% (the most fought-over take-home dishes); "heavy" scales the
 *    entire list by +50% (the "add five people" rule of thumb for hosts
 *    who send everyone home with to-go plates).
 *  - Roast at 325°F / 165°C following the USDA-style weight timetable
 *    (~13–22 min per lb, tapering as the bird gets bigger), plus 45 min resting.
 *  - Fridge thaw: 1 day per 4 lbs of turkey.
 */
(function (root) {
    'use strict';

    /* --- Per-person constants (same quantities as Omni Calculator) --- */
    const RATIOS = {
        turkeyLbsPerAdult: 1.5,      // lbs of whole turkey per equivalent adult (0.680389 kg)
        stuffingLbsPerAdult: 0.25,   // lbs (0.113398 kg)
        potatoesLbsPerAdult: 0.3307, // lbs (0.15 kg per person)
        veggiesOzPerAdult: 3.5,      // oz (0.0992233 kg)
        cranberryFlOzPerAdult: 2.0,  // US fl oz (0.05914706 L)
        cheeseOzPerAdult: 2.0,       // oz (0.056699 kg)
        appetizersPerAdult: 7,       // pieces (children count as half)
        rollsPerAdult: 2,            // pieces (kids get 1)
        rollsPerChild: 1,
        piesPerAdults: 6,            // 1 pie per 6 equivalent adults
        wineLitersPerAdult: 0.709765 // L per adult, kids don't drink (3 US cups)
    };

    const WINE_BOTTLE_LITERS = 0.75;   // standard 750 ml wine bottle

    // Leftover modes. "light" buffers the turkey and the take-home
    // favorites (potatoes, dinner rolls) by +30%; "heavy" scales the whole
    // grocery list by +50% — the field-tested "add five people" advice for
    // big-eater families where everything gets packed up.
    const LEFTOVER_MODES = {
        none:  { turkey: 1.0, hotSides: 1.0, sides: 1.0 },
        light: { turkey: 1.3, hotSides: 1.3, sides: 1.0 },
        heavy: { turkey: 1.5, hotSides: 1.5, sides: 1.5 }
    };
    const REST_MINUTES = 45;          // turkey resting time
    const THAW_DAYS_PER_LB = 1 / 4;   // fridge thaw: 1 day per 4 lbs
    const WATER_THAW_MIN_PER_LB = 30; // cold-water thaw: 30 min per lb, change water every 30 min

    /** Cold-water thaw time in minutes (submerge in cold water, change it every 30 min). */
    const coldWaterThawMinutes = (lbs) => lbs * WATER_THAW_MIN_PER_LB;

    /**
     * USDA-style roast timetable (same lookup as Omni Calculator):
     * minutes of roasting at 325°F / 165°C per 4-oz weight band,
     * starting at 96 oz (6 lb) up to 384 oz (24 lb). Clamped outside.
     */
    const ROAST_TABLE_FIRST_OZ = 96;
    const ROAST_TABLE_BAND_OZ = 4;
    const ROAST_TABLE_MINUTES = [
        135, 139, 143, 147, 151, 156, 161, 165, 167, 169, 171, 173,
        175, 177, 179, 181, 183, 185, 187, 189, 190, 192, 194, 195,
        197, 201, 205, 208, 212, 216, 220, 224, 228, 232, 236, 240,
        243, 247, 251, 255, 257, 259, 261, 263, 265, 267, 269, 271,
        273, 275, 277, 279, 281, 282, 284, 285, 287, 289, 291, 293,
        295, 297, 299, 301, 303, 305, 307, 309, 311, 312, 314, 315
    ];

    /**
     * Roast time for a whole turkey, in minutes.
     * @param {number} lbs   Total turkey weight in pounds.
     * @param {Object} [opts] Optional factors: done (1 | 1.06 well done),
     *                        speed (0.9 fast | 1 | 1.5 slow), cavity
     *                        (0 unstuffed | 15 partially | 45 stuffed).
     */
    function roastMinutesForWeight(lbs, opts = {}) {
        const done = opts.done !== undefined ? opts.done : 1;
        const speed = opts.speed !== undefined ? opts.speed : 1;
        const cavity = opts.cavity !== undefined ? opts.cavity : 0;

        const oz = lbs * 16;
        const idx = Math.floor((oz - ROAST_TABLE_FIRST_OZ) / ROAST_TABLE_BAND_OZ);
        const clamped = Math.max(0, Math.min(ROAST_TABLE_MINUTES.length - 1, idx));

        return ROAST_TABLE_MINUTES[clamped] * done * speed + cavity;
    }

    const MINUTE_MS = 60 * 1000;

    /* --- Date helpers --- */
    const pad = (n) => String(n).padStart(2, '0');

    /** Serialize a Date into the value format of <input type="datetime-local">. */
    const toInputValue = (d) =>
        `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}` +
        `T${pad(d.getHours())}:${pad(d.getMinutes())}`;

    /** Thanksgiving = 4th Thursday of November, dinner at 4:00 PM. */
    const thanksgivingOf = (year) => {
        const first = new Date(year, 10, 1);
        const firstThursday = 1 + ((4 - first.getDay() + 7) % 7);
        return new Date(year, 10, firstThursday + 21, 16, 0);
    };

    /** The upcoming (or current year's) Thanksgiving, relative to `now`. */
    const nearestThanksgiving = (now = new Date()) => {
        const thisYear = thanksgivingOf(now.getFullYear());
        return now > thisYear ? thanksgivingOf(now.getFullYear() + 1) : thisYear;
    };

    /* --- Core engine --- */

    /**
     * Calculate groceries and the reverse-engineered cooking timeline.
     *
     * @param {Object} params
     * @param {number} params.adults       Number of adults.
     * @param {number} params.children     Number of children (under 12).
     * @param {string} [params.leftoverMode] 'none' | 'light' (+30% turkey,
     *        potatoes, rolls) |
     *        'heavy' (+50% on everything). Legacy boolean `leftovers` still
     *        accepted: true -> 'light', false -> 'none'.
     * @param {Date} params.dinnerTime     Target sit-down time.
     * @returns {Object} grocery quantities + timeline milestones.
     */
    function planFeast({ adults = 0, children = 0, leftovers = undefined, leftoverMode = undefined, dinnerTime }) {
        const A = Number(adults) || 0;
        const C = Number(children) || 0;
        const target = dinnerTime instanceof Date ? dinnerTime : new Date(dinnerTime);

        // Equivalent adults: children count as half
        const E = A + (C / 2);

        const mode = leftoverMode || (leftovers === true ? 'light' : 'none');
        const { turkey: turkeyMult, hotSides: hotSideMult, sides: sideMult } =
            LEFTOVER_MODES[mode] || LEFTOVER_MODES.none;

        /* --- A. Groceries --- */
        const turkeyLbs = E * RATIOS.turkeyLbsPerAdult * turkeyMult;

        const grocery = {
            turkeyLbs,
            stuffingLbs: E * RATIOS.stuffingLbsPerAdult * sideMult,
            potatoesLbs: E * RATIOS.potatoesLbsPerAdult * hotSideMult,
            veggiesOz: E * RATIOS.veggiesOzPerAdult * sideMult,
            cranberryFlOz: E * RATIOS.cranberryFlOzPerAdult * sideMult,
            cheeseOz: E * RATIOS.cheeseOzPerAdult * sideMult,
            appetizers: Math.ceil(E * RATIOS.appetizersPerAdult * sideMult),
            rolls: Math.ceil((A * RATIOS.rollsPerAdult + C * RATIOS.rollsPerChild) * hotSideMult),
            pies: Math.max(1, Math.ceil(E * sideMult / RATIOS.piesPerAdults)),
            wineBottles: A * RATIOS.wineLitersPerAdult * sideMult / WINE_BOTTLE_LITERS
        };

        /* --- B. Timeline, reverse-engineered from dinner time --- */
        // 1. Resting: pull the bird 45 minutes before dinner
        const timeToRest = new Date(target.getTime() - REST_MINUTES * MINUTE_MS);

        // 2. Oven: roast time from the USDA weight timetable
        const cookMinutes = roastMinutesForWeight(turkeyLbs);
        const timeToOven = new Date(timeToRest.getTime() - cookMinutes * MINUTE_MS);

        // 3. Thaw: fridge thaw = 1 day per 4 lbs
        const thawDays = turkeyLbs * THAW_DAYS_PER_LB;
        const timeToThaw = new Date(timeToOven.getTime() - thawDays * 24 * 60 * MINUTE_MS);

        const timeline = {
            restAt: timeToRest,
            ovenAt: timeToOven,
            thawAt: timeToThaw,
            thawDays,
            cookMinutes
        };

        return { equivalentAdults: E, grocery, timeline };
    }

    /* --- Formatting helpers --- */

    /** Round to `decimals` places and drop trailing zeros (17.6, not "17.60"). */
    const formatNum = (num, decimals = 1) => Number(num.toFixed(decimals));

    /** E.g. "Thu, Nov 26, 3:15 PM" */
    const formatDate = (dateObj) =>
        new Intl.DateTimeFormat('en-US', {
            weekday: 'short',
            month: 'short',
            day: 'numeric',
            hour: 'numeric',
            minute: '2-digit'
        }).format(dateObj);

    /* --- Calendar integration --- */

    /** Format a Date as an ICS UTC timestamp: YYYYMMDDTHHMMSSZ */
    const toICSDate = (d) => d.toISOString().replace(/[-:]/g, '').replace(/\.\d{3}Z$/, 'Z');

    const escapeICS = (s) =>
        String(s).replace(/\\/g, '\\\\').replace(/;/g, '\\;').replace(/,/g, '\\,');

    /**
     * URL that opens Google Calendar's "create event" form pre-filled
     * with this event. No API key or sign-in integration required.
     */
    function buildGoogleCalendarUrl(event) {
        const params = new URLSearchParams({
            action: 'TEMPLATE',
            text: event.title,
            dates: `${toICSDate(event.start)}/${toICSDate(event.end)}`,
            details: event.details || ''
        });
        return `https://calendar.google.com/calendar/render?${params.toString()}`;
    }

    /**
     * RFC 5545 .ics content with a pop-up reminder (VALARM) per event.
     * Importable into Google, Apple and Outlook Calendar.
     */
    function buildICS(events, prodId = '-//HostCalc Pro//Thanksgiving Planner//EN') {
        const now = toICSDate(new Date());
        const lines = ['BEGIN:VCALENDAR', 'VERSION:2.0', `PRODID:${prodId}`, 'CALSCALE:GREGORIAN'];
        events.forEach((ev) => {
            lines.push(
                'BEGIN:VEVENT',
                `UID:${ev.uid}@hostcalc.pro`,
                `DTSTAMP:${now}`,
                `DTSTART:${toICSDate(ev.start)}`,
                `DTEND:${toICSDate(ev.end)}`,
                `SUMMARY:${escapeICS(ev.title)}`
            );
            if (ev.details) lines.push(`DESCRIPTION:${escapeICS(ev.details)}`);
            lines.push(
                'BEGIN:VALARM',
                `TRIGGER:${ev.reminder || '-PT30M'}`,
                'ACTION:DISPLAY',
                `DESCRIPTION:${escapeICS(ev.title)}`,
                'END:VALARM',
                'END:VEVENT'
            );
        });
        lines.push('END:VCALENDAR');
        return lines.join('\r\n');
    }

    /**
     * Turn a planFeast result into calendar events:
     * thaw, oven, rest milestones plus the dinner itself.
     */
    function milestoneEvents(plan, dinnerTime) {
        const lb = formatNum(plan.grocery.turkeyLbs);
        const mins = Math.round(plan.timeline.cookMinutes);
        const at = (d, minutes) => new Date(d.getTime() + minutes * MINUTE_MS);

        return [
            {
                uid: 'thaw',
                title: `Thaw ${lb} lb turkey in the fridge`,
                start: plan.timeline.thawAt,
                end: at(plan.timeline.thawAt, 30),
                details: `Fridge thaw needs about ${formatNum(plan.timeline.thawDays)} days (1 day per 4 lb). Planned with HostCalc Pro.`
            },
            {
                uid: 'oven',
                title: `Put ${lb} lb turkey in the oven (325°F / 165°C)`,
                start: plan.timeline.ovenAt,
                end: plan.timeline.restAt,
                details: `Roast about ${mins} minutes until the internal temperature reaches 165°F. Planned with HostCalc Pro.`
            },
            {
                uid: 'rest',
                title: 'Pull turkey at 165°F and let it rest',
                start: plan.timeline.restAt,
                end: dinnerTime,
                details: 'Take the bird out and rest it 45 minutes before dinner. Planned with HostCalc Pro.'
            },
            {
                uid: 'dinner',
                title: 'Thanksgiving dinner',
                start: dinnerTime,
                end: at(dinnerTime, 120),
                details: 'Dinner is served. Planned with HostCalc Pro.',
                reminder: '-PT60M'
            }
        ];
    }

    const api = {
        RATIOS,
        WINE_BOTTLE_LITERS,
        LEFTOVER_MODES,
        REST_MINUTES,
        THAW_DAYS_PER_LB,
        WATER_THAW_MIN_PER_LB,
        coldWaterThawMinutes,
        roastMinutesForWeight,
        toInputValue,
        thanksgivingOf,
        nearestThanksgiving,
        planFeast,
        formatNum,
        formatDate,
        buildGoogleCalendarUrl,
        buildICS,
        milestoneEvents
    };

    if (typeof module !== 'undefined' && module.exports) {
        module.exports = api;
    } else {
        root.ThanksgivingPlanner = api;
    }
})(this);
