const fieldIds = {
  projectName: 'Nome do empreendimento',
  responsible: 'Responsável técnico',
  location: 'Localização',
  description: 'Descrição do projeto',
  zoning: 'Zoneamento / Legislação',
  stage: 'Estágio do projeto',
  urbanContext: 'Características urbanísticas',
  socioeconomic: 'Perfil socioeconômico',
  infrastructure: 'Infraestrutura existente',
  positiveImpacts: 'Impactos positivos',
  negativeImpacts: 'Impactos negativos',
  mitigation: 'Medidas mitigadoras / compensatórias',
  mobility: 'Mobilidade e trânsito',
  publicEquipment: 'Equipamentos urbanos',
  sanitation: 'Saneamento, drenagem e energia',
  security: 'Segurança pública e defesa civil',
  communication: 'Estratégia de comunicação',
  publicParticipation: 'Audiências e consultas públicas',
  demands: 'Demandas e encaminhamentos',
  indicators: 'Indicadores de acompanhamento',
  monitoringTeam: 'Equipe de monitoramento',
  timeline: 'Cronograma de avaliação',
};

const reportPreview = document.getElementById('reportPreview');
const generateReportButton = document.getElementById('generateReport');
const downloadReportButton = document.getElementById('downloadReport');
const clearFormButton = document.getElementById('clearForm');

let lastReportHtml = '';

function getFieldValue(id) {
  const element = document.getElementById(id);
  if (!element) return '';
  if (element.tagName === 'SELECT') {
    return element.value ? element.options[element.selectedIndex].text : '';
  }
  return element.value.trim();
}

function formatParagraphs(text) {
  if (!text) return '<p><em>Não informado.</em></p>';

  const bulletMatch = text.trim().startsWith('-') || text.includes('\n-');
  if (bulletMatch) {
    const items = text
      .split('\n')
      .map((line) => line.replace(/^[-•]\s*/, '').trim())
      .filter(Boolean);
    if (items.length === 0) {
      return '<p><em>Não informado.</em></p>';
    }
    const listItems = items.map((item) => `<li>${escapeHtml(item)}</li>`);
    return `<ul>${listItems.join('')}</ul>`;
  }

  const paragraphs = text
    .split(/\n{2,}/)
    .map((paragraph) => paragraph.trim())
    .filter(Boolean)
    .map((paragraph) =>
      `<p>${escapeHtml(paragraph).replace(/\n/g, '<br />')}</p>`
    );

  if (paragraphs.length === 0) {
    return '<p><em>Não informado.</em></p>';
  }

  return paragraphs.join('');
}

function escapeHtml(text) {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function buildSection(title, content) {
  return `
    <section>
      <h3>${title}</h3>
      ${formatParagraphs(content)}
    </section>
  `;
}

function validateForm() {
  const projectName = getFieldValue('projectName');
  if (!projectName) {
    document.getElementById('projectName').focus();
    reportPreview.innerHTML =
      '<p class="warning">Informe pelo menos o nome do empreendimento para gerar o relatório.</p>';
    return false;
  }
  return true;
}

function generateReport() {
  if (!validateForm()) return;

  const reportSections = [
    {
      title: '1. Identificação do Empreendimento',
      content: [
        ['Nome do empreendimento', getFieldValue('projectName')],
        ['Responsável técnico', getFieldValue('responsible')],
        ['Localização', getFieldValue('location')],
        ['Descrição do projeto', getFieldValue('description')],
        ['Zoneamento / Legislação aplicável', getFieldValue('zoning')],
        ['Estágio do projeto', getFieldValue('stage')],
      ]
        .map(([label, value]) => `<p><strong>${label}:</strong> ${value ? escapeHtml(value) : '<em>Não informado.</em>'}</p>`)
        .join(''),
    },
    {
      title: '2. Caracterização da Área de Influência',
      content:
        buildSection(fieldIds.urbanContext, getFieldValue('urbanContext')) +
        buildSection(fieldIds.socioeconomic, getFieldValue('socioeconomic')) +
        buildSection(fieldIds.infrastructure, getFieldValue('infrastructure')),
    },
    {
      title: '3. Avaliação de Impactos',
      content:
        buildSection(fieldIds.positiveImpacts, getFieldValue('positiveImpacts')) +
        buildSection(fieldIds.negativeImpacts, getFieldValue('negativeImpacts')) +
        buildSection(fieldIds.mitigation, getFieldValue('mitigation')),
    },
    {
      title: '4. Serviços Públicos e Infraestrutura',
      content:
        buildSection(fieldIds.mobility, getFieldValue('mobility')) +
        buildSection(fieldIds.publicEquipment, getFieldValue('publicEquipment')) +
        buildSection(fieldIds.sanitation, getFieldValue('sanitation')) +
        buildSection(fieldIds.security, getFieldValue('security')),
    },
    {
      title: '5. Participação Social e Comunicação',
      content:
        buildSection(fieldIds.communication, getFieldValue('communication')) +
        buildSection(fieldIds.publicParticipation, getFieldValue('publicParticipation')) +
        buildSection(fieldIds.demands, getFieldValue('demands')),
    },
    {
      title: '6. Plano de Monitoramento',
      content:
        buildSection(fieldIds.indicators, getFieldValue('indicators')) +
        buildSection(fieldIds.monitoringTeam, getFieldValue('monitoringTeam')) +
        buildSection(fieldIds.timeline, getFieldValue('timeline')),
    },
  ];

  const generatedHtml = reportSections
    .map(
      (section) => `
        <article class="report-section">
          <h2>${section.title}</h2>
          ${section.content}
        </article>
      `
    )
    .join('\n');

  lastReportHtml = `
    <div class="report">
      <header>
        <h1>Estudo de Impacto de Vizinhança</h1>
        <p><strong>Empreendimento:</strong> ${escapeHtml(getFieldValue('projectName'))}</p>
        ${getFieldValue('responsible') ? `<p><strong>Responsável técnico:</strong> ${escapeHtml(getFieldValue('responsible'))}</p>` : ''}
      </header>
      ${generatedHtml}
      <footer>
        <p class="reference">Referência: Estatuto da Cidade (Lei nº 10.257/2001)</p>
      </footer>
    </div>
  `;

  reportPreview.innerHTML = lastReportHtml;
  downloadReportButton.disabled = false;
  window.scrollTo({ top: reportPreview.offsetTop - 100, behavior: 'smooth' });
}

function downloadReport() {
  if (!lastReportHtml) return;

  const reportWindow = window.open('', '_blank', 'noopener');
  if (!reportWindow) {
    alert('Não foi possível abrir a janela de impressão. Verifique o bloqueio de pop-ups.');
    return;
  }

  reportWindow.document.write(`
    <!DOCTYPE html>
    <html lang="pt-BR">
      <head>
        <meta charset="UTF-8" />
        <title>Relatório EIV</title>
        <style>
          body {
            font-family: "Inter", system-ui, -apple-system, "Segoe UI", sans-serif;
            margin: 2cm;
            color: #0f172a;
          }
          h1, h2, h3 {
            color: #0b3d62;
          }
          h1 {
            text-align: center;
            margin-bottom: 0.5cm;
          }
          article + article {
            margin-top: 1.5cm;
          }
          ul {
            padding-left: 1.2cm;
          }
          .reference {
            font-size: 0.85rem;
            color: #475569;
            margin-top: 2cm;
          }
        </style>
      </head>
      <body>
        ${lastReportHtml}
      </body>
    </html>
  `);
  reportWindow.document.close();
  reportWindow.focus();
  reportWindow.print();
}

function clearForm() {
  const inputs = document.querySelectorAll(
    'input, textarea, select'
  );
  inputs.forEach((input) => {
    if (input.tagName === 'SELECT') {
      input.selectedIndex = 0;
    } else {
      input.value = '';
    }
  });

  reportPreview.innerHTML =
    'Preencha os campos e clique em "Gerar relatório" para visualizar o Estudo de Impacto de Vizinhança.';
  downloadReportButton.disabled = true;
  lastReportHtml = '';
}

function handleInputAutosave() {
  const formState = {};
  Object.keys(fieldIds).forEach((key) => {
    formState[key] = getFieldValue(key);
  });
  localStorage.setItem('eiv-form', JSON.stringify(formState));
}

function restoreForm() {
  const saved = localStorage.getItem('eiv-form');
  if (!saved) return;
  try {
    const data = JSON.parse(saved);
    Object.entries(data).forEach(([key, value]) => {
      const element = document.getElementById(key);
      if (!element) return;
      if (element.tagName === 'SELECT') {
        const optionIndex = Array.from(element.options).findIndex(
          (option) => option.text === value
        );
        element.selectedIndex = optionIndex >= 0 ? optionIndex : 0;
      } else {
        element.value = value;
      }
    });
  } catch (error) {
    console.error('Erro ao restaurar o formulário:', error);
  }
}

function init() {
  restoreForm();

  generateReportButton.addEventListener('click', generateReport);
  downloadReportButton.addEventListener('click', downloadReport);
  clearFormButton.addEventListener('click', clearForm);

  document
    .querySelectorAll('input, textarea, select')
    .forEach((element) =>
      element.addEventListener('change', () => {
        handleInputAutosave();
        downloadReportButton.disabled = true;
      })
    );

  if (getFieldValue('projectName')) {
    generateReport();
  }
}

document.addEventListener('DOMContentLoaded', init);
