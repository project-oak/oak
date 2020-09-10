import React from 'react';
import { makeStyles, Theme } from '@material-ui/core/styles';
import AppBar from '@material-ui/core/AppBar';
import Tabs from '@material-ui/core/Tabs';
import Tab from '@material-ui/core/Tab';

interface TabPanelProps {
  children?: React.ReactNode;
  index: number;
  value: number;
}

const useTabPanelStyles = makeStyles((theme: Theme) => ({
  root: {
    display: 'flex',
    height: '100%',
  },
}));

function TabPanel({ children, value, index, ...other }: TabPanelProps) {
  const classes = useTabPanelStyles();
  const isActive = value === index;
  return (
    <div
      role="tabpanel"
      hidden={!isActive}
      id={`simple-tabpanel-${index}`}
      aria-labelledby={`simple-tab-${index}`}
      className={isActive ? classes.root : undefined}
      {...other}
    >
      {isActive ? children : undefined}
    </div>
  );
}

function a11yProps(index: any) {
  return {
    id: `simple-tab-${index}`,
    'aria-controls': `simple-tabpanel-${index}`,
  };
}

const useMainTabsStyles = makeStyles((theme: Theme) => ({
  root: {
    flexGrow: 1,
    backgroundColor: theme.palette.background.paper,
  },
}));

interface Tab {
  render: () => JSX.Element;
  label: string;
}

interface MainTabsProps {
  tabs: Tab[];
}

export default function MainTabs({ tabs }: MainTabsProps) {
  const classes = useMainTabsStyles();
  const [activeTab, setActiveTab] = React.useState(0);

  const handleChange = (event: React.ChangeEvent<{}>, newValue: number) => {
    setActiveTab(newValue);
  };

  return (
    <nav className={classes.root}>
      <AppBar position="static">
        <Tabs value={activeTab} onChange={handleChange}>
          {tabs.map((tab, index) => (
            <Tab label={tab.label} {...a11yProps(index)} />
          ))}
        </Tabs>
      </AppBar>
      {tabs.map((tab, index) => (
        <TabPanel value={activeTab} index={index}>
          {tab.render()}
        </TabPanel>
      ))}
    </nav>
  );
}
