/**
 * Injects jsCoq into an existing page.
 * This script has to be at the end of the body so that it runs after
 * the page DOM has loaded.
 */

function jsCoqInject() {
    $(document.body).attr('id', 'ide-wrapper').addClass('toggled')
        .addClass(isTerse() ? 'terse' : 'full')
        .append($('<div id="jscoq-plug">').on('click', jsCoqStart));
}

var jsCoqShow = location.search === '?jscoq=on' ||
                location.search !== '?jscoq=off' && localStorage.jsCoqShow === 'true';

var jscoq_ids  = ['#main > div.code, #main > div.HIDEFROMHTML > div.code'];
var jscoq_opts = {
    layout:    'flex',
    show:      jsCoqShow,
    focus:     false,
    replace:   true,
    editor:    { mode: { 'company-coq': true }, className: 'jscoq code-tight' },
    init_pkgs: ['init'],
    all_pkgs:  { '+': ['coq'], '../../coq-pkgs': ['software-foundations'] },
    init_import: ['utf8'],
    implicit_libs: true
};

async function jsCoqLoad() {
    // - remove empty code fragments (coqdoc generates some spurious ones)
    $('#main > div.code').each(function() {
        if ($(this).text().match(/^\s*$/)) $(this).remove();
    });

    // - make page div focusable so that keyboard scrolling works
    var page = document.querySelector('#page');
    page.setAttribute('tabindex', -1);
    page.focus();

    // - set presenter keyboard bindings to page-up/page-down to allow editing
    if (typeof KEYS !== 'undefined')
        Object.assign(KEYS, {
            next: 34,        // PageDown
            prev: 33         // PageUp
        });

    // - load and start jsCoq
    await JsCoq.load(jscoq_opts.base_path);

    Deprettify.REPLACES.push(   // LF,PLF define their own versions (for Imp)
        [/∨/g, '\\/'], [/∧/g, '/\\'], [/↔/g, '<->'],
        [/≤/g, '<='], [/≥/g, '>='], [/≠/g, '<>'], [/∈/g, '\\in']);

    var coq = await JsCoq.start(jscoq_ids, jscoq_opts);
    window.coq = coq;
    window.addEventListener('beforeunload', () => { localStorage.jsCoqShow = coq.layout.isVisible(); })

    // - close button (replaces jsCoq's bulky power button)
    $('#panel-wrapper #toolbar').append($('<button>').addClass('close').text('×')
        .on('click', () => coq.layout.hide()));
}

function jsCoqStart() {
    coq.layout.show();
}

function isTerse() {
    return $('[src$="/slides.js"]').length > 0;
}

if (location.search !== '?jscoq=no') {
    window.addEventListener('DOMContentLoaded', () => {
        jsCoqInject();
        jsCoqLoad();
    });
}
